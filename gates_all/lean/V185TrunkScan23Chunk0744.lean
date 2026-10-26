import V185TrunkScan23Chunk0743

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4399314 : List Nat := [3, 2, 2, 2, 1, 2, 1, 1, 1, 2, 6]
def baseStart_4399314 : Nat := 118140960795 + 4399314 * 2 ^ 59
def prefixEnd_4399314 : Nat := 4983230072969 + 3 ^ 40 * 4399314 * 2
def baseEnd_4399314 : Nat := 2258962632053905897442929

theorem tailTrace_4399314 : CollatzResearch.WordTrace tailWord_4399314 prefixEnd_4399314 2258962632053905897442929 := by
  unfold tailWord_4399314
  simp only [CollatzResearch.WordTrace]
  refine ⟨40114040896011048964709249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106970775722696130572557997 40114040896011048964709249)
  ·
    refine ⟨30085530672008286723531937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40114040896011048964709249 30085530672008286723531937)
    ·
      refine ⟨22564148004006215042648953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30085530672008286723531937 22564148004006215042648953)
      ·
        refine ⟨16923111003004661281986715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22564148004006215042648953 16923111003004661281986715)
        ·
          refine ⟨25384666504506991922980073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16923111003004661281986715 25384666504506991922980073)
          ·
            refine ⟨19038499878380243942235055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25384666504506991922980073 19038499878380243942235055)
            ·
              refine ⟨28557749817570365913352583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19038499878380243942235055 28557749817570365913352583)
              ·
                refine ⟨42836624726355548870028875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28557749817570365913352583 42836624726355548870028875)
                ·
                  refine ⟨64254937089533323305043313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42836624726355548870028875 64254937089533323305043313)
                  ·
                    refine ⟨48191202817149992478782485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 64254937089533323305043313 48191202817149992478782485)
                    ·
                      refine ⟨2258962632053905897442929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48191202817149992478782485 2258962632053905897442929)
                      ·
                        rfl

theorem cell23_4399314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_4399314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4399314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4399314 prefixEnd_4399314 := by exact prefixLift 4399314
  have htrace : WordTrace (prefixWord ++ tailWord_4399314) baseStart_4399314 baseEnd_4399314 := by
    simpa [prefixWord, tailWord_4399314, baseEnd_4399314] using wordTrace_append hprefix tailTrace_4399314
  have hstable : (prefixWord ++ tailWord_4399314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4399314).length < 2 ^ (prefixWord ++ tailWord_4399314).sum := by decide
  have hdescent : baseEnd_4399314 < baseStart_4399314 := by decide
  rcases family_descends (prefixWord ++ tailWord_4399314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4399321 : List Nat := [1, 2, 1, 2, 3, 1, 3, 3, 3, 1, 3]
def baseStart_4399321 : Nat := 118140960795 + 4399321 * 2 ^ 59
def prefixEnd_4399321 : Nat := 4983230072969 + 3 ^ 40 * 4399321 * 2
def baseEnd_4399321 : Nat := 2258966226418487370055397

theorem tailTrace_4399321 : CollatzResearch.WordTrace tailWord_4399321 prefixEnd_4399321 2258966226418487370055397 := by
  unfold tailWord_4399321
  simp only [CollatzResearch.WordTrace]
  refine ⟨160456418895018836054341817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106970945930012557369561211 160456418895018836054341817)
  ·
    refine ⟨120342314171264127040756363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160456418895018836054341817 120342314171264127040756363)
    ·
      refine ⟨180513471256896190561134545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120342314171264127040756363 180513471256896190561134545)
      ·
        refine ⟨135385103442672142920850909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180513471256896190561134545 135385103442672142920850909)
        ·
          refine ⟨50769413791002053595319091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135385103442672142920850909 50769413791002053595319091)
          ·
            refine ⟨76154120686503080392978637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50769413791002053595319091 76154120686503080392978637)
            ·
              refine ⟨28557795257438655147366989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76154120686503080392978637 28557795257438655147366989)
              ·
                refine ⟨10709173221539495680262621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28557795257438655147366989 10709173221539495680262621)
                ·
                  refine ⟨4015939958077310880098483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10709173221539495680262621 4015939958077310880098483)
                  ·
                    refine ⟨6023909937115966320147725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4015939958077310880098483 6023909937115966320147725)
                    ·
                      refine ⟨2258966226418487370055397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6023909937115966320147725 2258966226418487370055397)
                      ·
                        rfl

theorem cell23_4399321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 3, 3, 1, 3].length) (baseStart_4399321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4399321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4399321 prefixEnd_4399321 := by exact prefixLift 4399321
  have htrace : WordTrace (prefixWord ++ tailWord_4399321) baseStart_4399321 baseEnd_4399321 := by
    simpa [prefixWord, tailWord_4399321, baseEnd_4399321] using wordTrace_append hprefix tailTrace_4399321
  have hstable : (prefixWord ++ tailWord_4399321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4399321).length < 2 ^ (prefixWord ++ tailWord_4399321).sum := by decide
  have hdescent : baseEnd_4399321 < baseStart_4399321 := by decide
  rcases family_descends (prefixWord ++ tailWord_4399321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4399344 : List Nat := [2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 4]
def baseStart_4399344 : Nat := 118140960795 + 4399344 * 2 ^ 59
def prefixEnd_4399344 : Nat := 4983230072969 + 3 ^ 40 * 4399344 * 2
def baseEnd_4399344 : Nat := 2258978036473540780067791

theorem tailTrace_4399344 : CollatzResearch.WordTrace tailWord_4399344 prefixEnd_4399344 2258978036473540780067791 := by
  unfold tailWord_4399344
  simp only [CollatzResearch.WordTrace]
  refine ⟨80228628886967755491214543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106971505182623673988286057 80228628886967755491214543)
  ·
    refine ⟨120342943330451633236821815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80228628886967755491214543 120342943330451633236821815)
    ·
      refine ⟨180514414995677449855232723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120342943330451633236821815 180514414995677449855232723)
      ·
        refine ⟨270771622493516174782849085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180514414995677449855232723 270771622493516174782849085)
        ·
          refine ⟨101539358435068565543568407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 270771622493516174782849085 101539358435068565543568407)
          ·
            refine ⟨152309037652602848315352611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101539358435068565543568407 152309037652602848315352611)
            ·
              refine ⟨228463556478904272473028917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152309037652602848315352611 228463556478904272473028917)
              ·
                refine ⟨21418458419897275544346461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 228463556478904272473028917 21418458419897275544346461)
                ·
                  refine ⟨8031921907461478329129923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21418458419897275544346461 8031921907461478329129923)
                  ·
                    refine ⟨12047882861192217493694885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8031921907461478329129923 12047882861192217493694885)
                    ·
                      refine ⟨2258978036473540780067791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12047882861192217493694885 2258978036473540780067791)
                      ·
                        rfl

theorem cell23_4399344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 4].length) (baseStart_4399344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4399344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4399344 prefixEnd_4399344 := by exact prefixLift 4399344
  have htrace : WordTrace (prefixWord ++ tailWord_4399344) baseStart_4399344 baseEnd_4399344 := by
    simpa [prefixWord, tailWord_4399344, baseEnd_4399344] using wordTrace_append hprefix tailTrace_4399344
  have hstable : (prefixWord ++ tailWord_4399344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4399344).length < 2 ^ (prefixWord ++ tailWord_4399344).sum := by decide
  have hdescent : baseEnd_4399344 < baseStart_4399344 := by decide
  rcases family_descends (prefixWord ++ tailWord_4399344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4399361 : List Nat := [1, 2, 4, 1, 1, 2, 1, 5, 1, 1, 4]
def baseStart_4399361 : Nat := 118140960795 + 4399361 * 2 ^ 59
def prefixEnd_4399361 : Nat := 4983230072969 + 3 ^ 40 * 4399361 * 2
def baseEnd_4399361 : Nat := 2258986765644667213555213

theorem tailTrace_4399361 : CollatzResearch.WordTrace tailWord_4399361 prefixEnd_4399361 2258986765644667213555213 := by
  unfold tailWord_4399361
  simp only [CollatzResearch.WordTrace]
  refine ⟨160457877814873922885797937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106971918543249281923865291 160457877814873922885797937)
  ·
    refine ⟨120343408361155442164348453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160457877814873922885797937 120343408361155442164348453)
    ·
      refine ⟨22564389067716645405815335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120343408361155442164348453 22564389067716645405815335)
      ·
        refine ⟨33846583601574968108723003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22564389067716645405815335 33846583601574968108723003)
        ·
          refine ⟨50769875402362452163084505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33846583601574968108723003 50769875402362452163084505)
          ·
            refine ⟨38077406551771839122313379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50769875402362452163084505 38077406551771839122313379)
            ·
              refine ⟨57116109827657758683470069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38077406551771839122313379 57116109827657758683470069)
              ·
                refine ⟨5354635296342914876575319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57116109827657758683470069 5354635296342914876575319)
                ·
                  refine ⟨8031952944514372314862979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5354635296342914876575319 8031952944514372314862979)
                  ·
                    refine ⟨12047929416771558472294469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8031952944514372314862979 12047929416771558472294469)
                    ·
                      refine ⟨2258986765644667213555213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12047929416771558472294469 2258986765644667213555213)
                      ·
                        rfl

theorem cell23_4399361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 5, 1, 1, 4].length) (baseStart_4399361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4399361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4399361 prefixEnd_4399361 := by exact prefixLift 4399361
  have htrace : WordTrace (prefixWord ++ tailWord_4399361) baseStart_4399361 baseEnd_4399361 := by
    simpa [prefixWord, tailWord_4399361, baseEnd_4399361] using wordTrace_append hprefix tailTrace_4399361
  have hstable : (prefixWord ++ tailWord_4399361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4399361).length < 2 ^ (prefixWord ++ tailWord_4399361).sum := by decide
  have hdescent : baseEnd_4399361 < baseStart_4399361 := by decide
  rcases family_descends (prefixWord ++ tailWord_4399361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4399371 : List Nat := [1, 1, 1, 1, 5, 2, 2, 4, 2, 4]
def baseStart_4399371 : Nat := 118140960795 + 4399371 * 2 ^ 59
def prefixEnd_4399371 : Nat := 4983230072969 + 3 ^ 40 * 4399371 * 2
def baseEnd_4399371 : Nat := 752997300150404058143389

theorem tailTrace_4399371 : CollatzResearch.WordTrace tailWord_4399371 prefixEnd_4399371 752997300150404058143389 := by
  unfold tailWord_4399371
  simp only [CollatzResearch.WordTrace]
  refine ⟨160458242544837694593661967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106972161696558463062441311 160458242544837694593661967)
  ·
    refine ⟨240687363817256541890492951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160458242544837694593661967 240687363817256541890492951)
    ·
      refine ⟨361031045725884812835739427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240687363817256541890492951 361031045725884812835739427)
      ·
        refine ⟨541546568588827219253609141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 361031045725884812835739427 541546568588827219253609141)
        ·
          refine ⟨50769990805202551805025857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 541546568588827219253609141 50769990805202551805025857)
          ·
            refine ⟨38077493103901913853769393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50769990805202551805025857 38077493103901913853769393)
            ·
              refine ⟨28558119827926435390327045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38077493103901913853769393 28558119827926435390327045)
              ·
                refine ⟨5354647467736206635686321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28558119827926435390327045 5354647467736206635686321)
                ·
                  refine ⟨4015985600802154976764741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5354647467736206635686321 4015985600802154976764741)
                  ·
                    refine ⟨752997300150404058143389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4015985600802154976764741 752997300150404058143389)
                    ·
                      rfl

theorem cell23_4399371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 4, 2, 4].length) (baseStart_4399371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4399371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4399371 prefixEnd_4399371 := by exact prefixLift 4399371
  have htrace : WordTrace (prefixWord ++ tailWord_4399371) baseStart_4399371 baseEnd_4399371 := by
    simpa [prefixWord, tailWord_4399371, baseEnd_4399371] using wordTrace_append hprefix tailTrace_4399371
  have hstable : (prefixWord ++ tailWord_4399371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4399371).length < 2 ^ (prefixWord ++ tailWord_4399371).sum := by decide
  have hdescent : baseEnd_4399371 < baseStart_4399371 := by decide
  rcases family_descends (prefixWord ++ tailWord_4399371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4399374 : List Nat := [4, 1, 1, 2, 1, 2, 1, 1, 3, 1, 6]
def baseStart_4399374 : Nat := 118140960795 + 4399374 * 2 ^ 59
def prefixEnd_4399374 : Nat := 4983230072969 + 3 ^ 40 * 4399374 * 2
def baseEnd_4399374 : Nat := 2258993440893175662692653

theorem tailTrace_4399374 : CollatzResearch.WordTrace tailWord_4399374 prefixEnd_4399374 2258993440893175662692653 := by
  unfold tailWord_4399374
  simp only [CollatzResearch.WordTrace]
  refine ⟨20057293995478353263252647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106972234642551217404014117 20057293995478353263252647)
  ·
    refine ⟨30085940993217529894878971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20057293995478353263252647 30085940993217529894878971)
    ·
      refine ⟨45128911489826294842318457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30085940993217529894878971 45128911489826294842318457)
      ·
        refine ⟨33846683617369721131738843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45128911489826294842318457 33846683617369721131738843)
        ·
          refine ⟨50770025426054581697608265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33846683617369721131738843 50770025426054581697608265)
          ·
            refine ⟨38077519069540936273206199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50770025426054581697608265 38077519069540936273206199)
            ·
              refine ⟨57116278604311404409809299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38077519069540936273206199 57116278604311404409809299)
              ·
                refine ⟨85674417906467106614713949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57116278604311404409809299 85674417906467106614713949)
                ·
                  refine ⟨32127906714925164980517731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 85674417906467106614713949 32127906714925164980517731)
                  ·
                    refine ⟨48191860072387747470776597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32127906714925164980517731 48191860072387747470776597)
                    ·
                      refine ⟨2258993440893175662692653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48191860072387747470776597 2258993440893175662692653)
                      ·
                        rfl

theorem cell23_4399374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_4399374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4399374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4399374 prefixEnd_4399374 := by exact prefixLift 4399374
  have htrace : WordTrace (prefixWord ++ tailWord_4399374) baseStart_4399374 baseEnd_4399374 := by
    simpa [prefixWord, tailWord_4399374, baseEnd_4399374] using wordTrace_append hprefix tailTrace_4399374
  have hstable : (prefixWord ++ tailWord_4399374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4399374).length < 2 ^ (prefixWord ++ tailWord_4399374).sum := by decide
  have hdescent : baseEnd_4399374 < baseStart_4399374 := by decide
  rcases family_descends (prefixWord ++ tailWord_4399374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4399384 : List Nat := [2, 1, 2, 3, 1, 2, 4, 8]
def baseStart_4399384 : Nat := 118140960795 + 4399384 * 2 ^ 59
def prefixEnd_4399384 : Nat := 4983230072969 + 3 ^ 40 * 4399384 * 2
def baseEnd_4399384 : Nat := 83666613914804467539541

theorem tailTrace_4399384 : CollatzResearch.WordTrace tailWord_4399384 prefixEnd_4399384 83666613914804467539541 := by
  unfold tailWord_4399384
  simp only [CollatzResearch.WordTrace]
  refine ⟨80229358346895298906942603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106972477795860398542590137 80229358346895298906942603)
  ·
    refine ⟨120344037520342948360413905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80229358346895298906942603 120344037520342948360413905)
    ·
      refine ⟨90258028140257211270310429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120344037520342948360413905 90258028140257211270310429)
      ·
        refine ⟨33846760552596454226366411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90258028140257211270310429 33846760552596454226366411)
        ·
          refine ⟨50770140828894681339549617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33846760552596454226366411 50770140828894681339549617)
          ·
            refine ⟨38077605621671011004662213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50770140828894681339549617 38077605621671011004662213)
            ·
              refine ⟨7139551054063314563374165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38077605621671011004662213 7139551054063314563374165)
              ·
                refine ⟨83666613914804467539541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7139551054063314563374165 83666613914804467539541)
                ·
                  rfl

theorem cell23_4399384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 8].length) (baseStart_4399384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4399384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4399384 prefixEnd_4399384 := by exact prefixLift 4399384
  have htrace : WordTrace (prefixWord ++ tailWord_4399384) baseStart_4399384 baseEnd_4399384 := by
    simpa [prefixWord, tailWord_4399384, baseEnd_4399384] using wordTrace_append hprefix tailTrace_4399384
  have hstable : (prefixWord ++ tailWord_4399384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4399384).length < 2 ^ (prefixWord ++ tailWord_4399384).sum := by decide
  have hdescent : baseEnd_4399384 < baseStart_4399384 := by decide
  rcases family_descends (prefixWord ++ tailWord_4399384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4399399 : List Nat := [1, 1, 8, 1, 1, 1, 2, 1, 2, 3, 2]
def baseStart_4399399 : Nat := 118140960795 + 4399399 * 2 ^ 59
def prefixEnd_4399399 : Nat := 4983230072969 + 3 ^ 40 * 4399399 * 2
def baseEnd_4399399 : Nat := 2259006277909538064880039

theorem tailTrace_4399399 : CollatzResearch.WordTrace tailWord_4399399 prefixEnd_4399399 2259006277909538064880039 := by
  unfold tailWord_4399399
  simp only [CollatzResearch.WordTrace]
  refine ⟨160459263788736255375681251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106972842525824170250454167 160459263788736255375681251)
  ·
    refine ⟨240688895683104383063521877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160459263788736255375681251 240688895683104383063521877)
    ·
      refine ⟨2820572996286379489025647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 240688895683104383063521877 2820572996286379489025647)
      ·
        refine ⟨4230859494429569233538471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2820572996286379489025647 4230859494429569233538471)
        ·
          refine ⟨6346289241644353850307707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4230859494429569233538471 6346289241644353850307707)
          ·
            refine ⟨9519433862466530775461561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6346289241644353850307707 9519433862466530775461561)
            ·
              refine ⟨7139575396849898081596171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9519433862466530775461561 7139575396849898081596171)
              ·
                refine ⟨10709363095274847122394257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7139575396849898081596171 10709363095274847122394257)
                ·
                  refine ⟨8032022321456135341795693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10709363095274847122394257 8032022321456135341795693)
                  ·
                    refine ⟨3012008370546050753173385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8032022321456135341795693 3012008370546050753173385)
                    ·
                      refine ⟨2259006277909538064880039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3012008370546050753173385 2259006277909538064880039)
                      ·
                        rfl

theorem cell23_4399399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_4399399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4399399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4399399 prefixEnd_4399399 := by exact prefixLift 4399399
  have htrace : WordTrace (prefixWord ++ tailWord_4399399) baseStart_4399399 baseEnd_4399399 := by
    simpa [prefixWord, tailWord_4399399, baseEnd_4399399] using wordTrace_append hprefix tailTrace_4399399
  have hstable : (prefixWord ++ tailWord_4399399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4399399).length < 2 ^ (prefixWord ++ tailWord_4399399).sum := by decide
  have hdescent : baseEnd_4399399 < baseStart_4399399 := by decide
  rcases family_descends (prefixWord ++ tailWord_4399399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4399411 : List Nat := [1, 1, 1, 2, 5, 1, 3, 2, 1, 3, 3]
def baseStart_4399411 : Nat := 118140960795 + 4399411 * 2 ^ 59
def prefixEnd_4399411 : Nat := 4983230072969 + 3 ^ 40 * 4399411 * 2
def baseEnd_4399411 : Nat := 2259012439677392017929983

theorem tailTrace_4399411 : CollatzResearch.WordTrace tailWord_4399411 prefixEnd_4399411 2259012439677392017929983 := by
  unfold tailWord_4399411
  simp only [CollatzResearch.WordTrace]
  refine ⟨160459701464692781425118087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106973134309795187616745391 160459701464692781425118087)
  ·
    refine ⟨240689552197039172137677131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160459701464692781425118087 240689552197039172137677131)
    ·
      refine ⟨361034328295558758206515697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240689552197039172137677131 361034328295558758206515697)
      ·
        refine ⟨270775746221669068654886773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 361034328295558758206515697 270775746221669068654886773)
        ·
          refine ⟨25385226208281475186395635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 270775746221669068654886773 25385226208281475186395635)
          ·
            refine ⟨38077839312422212779593453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25385226208281475186395635 38077839312422212779593453)
            ·
              refine ⟨14279189742158329792347545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38077839312422212779593453 14279189742158329792347545)
              ·
                refine ⟨10709392306618747344260659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14279189742158329792347545 10709392306618747344260659)
                ·
                  refine ⟨16064088459928121016390989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10709392306618747344260659 16064088459928121016390989)
                  ·
                    refine ⟨6024033172473045381146621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16064088459928121016390989 6024033172473045381146621)
                    ·
                      refine ⟨2259012439677392017929983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6024033172473045381146621 2259012439677392017929983)
                      ·
                        rfl

theorem cell23_4399411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 2, 1, 3, 3].length) (baseStart_4399411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4399411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4399411 prefixEnd_4399411 := by exact prefixLift 4399411
  have htrace : WordTrace (prefixWord ++ tailWord_4399411) baseStart_4399411 baseEnd_4399411 := by
    simpa [prefixWord, tailWord_4399411, baseEnd_4399411] using wordTrace_append hprefix tailTrace_4399411
  have hstable : (prefixWord ++ tailWord_4399411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4399411).length < 2 ^ (prefixWord ++ tailWord_4399411).sum := by decide
  have hdescent : baseEnd_4399411 < baseStart_4399411 := by decide
  rcases family_descends (prefixWord ++ tailWord_4399411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4399472 : List Nat := [2, 1, 1, 1, 4, 5, 2, 1, 1, 3, 2]
def baseStart_4399472 : Nat := 118140960795 + 4399472 * 2 ^ 59
def prefixEnd_4399472 : Nat := 4983230072969 + 3 ^ 40 * 4399472 * 2
def baseEnd_4399472 : Nat := 2259043761997316279267203

theorem tailTrace_4399472 : CollatzResearch.WordTrace tailWord_4399472 prefixEnd_4399472 2259043761997316279267203 := by
  unfold tailWord_4399472
  simp only [CollatzResearch.WordTrace]
  refine ⟨80230963158735894421544335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106974617544981192562059113 80230963158735894421544335)
  ·
    refine ⟨120346444738103841632316503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80230963158735894421544335 120346444738103841632316503)
    ·
      refine ⟨180519667107155762448474755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120346444738103841632316503 180519667107155762448474755)
      ·
        refine ⟨270779500660733643672712133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180519667107155762448474755 270779500660733643672712133)
        ·
          refine ⟨50771156373887558188633525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 270779500660733643672712133 50771156373887558188633525)
          ·
            refine ⟨4759795910051958580184393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50771156373887558188633525 4759795910051958580184393)
            ·
              refine ⟨3569846932538968935138295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4759795910051958580184393 3569846932538968935138295)
              ·
                refine ⟨5354770398808453402707443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3569846932538968935138295 5354770398808453402707443)
                ·
                  refine ⟨8032155598212680104061165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5354770398808453402707443 8032155598212680104061165)
                  ·
                    refine ⟨3012058349329755039022937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8032155598212680104061165 3012058349329755039022937)
                    ·
                      refine ⟨2259043761997316279267203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3012058349329755039022937 2259043761997316279267203)
                      ·
                        rfl

theorem cell23_4399472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 2, 1, 1, 3, 2].length) (baseStart_4399472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4399472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4399472 prefixEnd_4399472 := by exact prefixLift 4399472
  have htrace : WordTrace (prefixWord ++ tailWord_4399472) baseStart_4399472 baseEnd_4399472 := by
    simpa [prefixWord, tailWord_4399472, baseEnd_4399472] using wordTrace_append hprefix tailTrace_4399472
  have hstable : (prefixWord ++ tailWord_4399472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4399472).length < 2 ^ (prefixWord ++ tailWord_4399472).sum := by decide
  have hdescent : baseEnd_4399472 < baseStart_4399472 := by decide
  rcases family_descends (prefixWord ++ tailWord_4399472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4399484 : List Nat := [2, 2, 2, 1, 1, 1, 2, 1, 1, 1, 9]
def baseStart_4399484 : Nat := 118140960795 + 4399484 * 2 ^ 59
def prefixEnd_4399484 : Nat := 4983230072969 + 3 ^ 40 * 4399484 * 2
def baseEnd_4399484 : Nat := 2259049923765170232317147

theorem tailTrace_4399484 : CollatzResearch.WordTrace tailWord_4399484 prefixEnd_4399484 2259049923765170232317147 := by
  unfold tailWord_4399484
  simp only [CollatzResearch.WordTrace]
  refine ⟨80231181996714157446262753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106974909328952209928350337 80231181996714157446262753)
  ·
    refine ⟨60173386497535618084697065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80231181996714157446262753 60173386497535618084697065)
    ·
      refine ⟨45130039873151713563522799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60173386497535618084697065 45130039873151713563522799)
      ·
        refine ⟨67695059809727570345284199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45130039873151713563522799 67695059809727570345284199)
        ·
          refine ⟨101542589714591355517926299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67695059809727570345284199 101542589714591355517926299)
          ·
            refine ⟨152313884571887033276889449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101542589714591355517926299 152313884571887033276889449)
            ·
              refine ⟨114235413428915274957667087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152313884571887033276889449 114235413428915274957667087)
              ·
                refine ⟨171353120143372912436500631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114235413428915274957667087 171353120143372912436500631)
                ·
                  refine ⟨257029680215059368654750947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 171353120143372912436500631 257029680215059368654750947)
                  ·
                    refine ⟨385544520322589052982126421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 257029680215059368654750947 385544520322589052982126421)
                    ·
                      refine ⟨2259049923765170232317147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 385544520322589052982126421 2259049923765170232317147)
                      ·
                        rfl

theorem cell23_4399484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_4399484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4399484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4399484 prefixEnd_4399484 := by exact prefixLift 4399484
  have htrace : WordTrace (prefixWord ++ tailWord_4399484) baseStart_4399484 baseEnd_4399484 := by
    simpa [prefixWord, tailWord_4399484, baseEnd_4399484] using wordTrace_append hprefix tailTrace_4399484
  have hstable : (prefixWord ++ tailWord_4399484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4399484).length < 2 ^ (prefixWord ++ tailWord_4399484).sum := by decide
  have hdescent : baseEnd_4399484 < baseStart_4399484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4399484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4399485 : List Nat := [1, 4, 1, 1, 2, 4, 1, 1, 4, 2, 2]
def baseStart_4399485 : Nat := 118140960795 + 4399485 * 2 ^ 59
def prefixEnd_4399485 : Nat := 4983230072969 + 3 ^ 40 * 4399485 * 2
def baseEnd_4399485 : Nat := 2259050437245824728404643

theorem tailTrace_4399485 : CollatzResearch.WordTrace tailWord_4399485 prefixEnd_4399485 2259050437245824728404643 := by
  unfold tailWord_4399485
  simp only [CollatzResearch.WordTrace]
  refine ⟨160462400466424692063311909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106974933644283128042207939 160462400466424692063311909)
  ·
    refine ⟨30086700087454629761870983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 160462400466424692063311909 30086700087454629761870983)
    ·
      refine ⟨45130050131181944642806475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30086700087454629761870983 45130050131181944642806475)
      ·
        refine ⟨67695075196772916964209713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45130050131181944642806475 67695075196772916964209713)
        ·
          refine ⟨50771306397579687723157285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67695075196772916964209713 50771306397579687723157285)
          ·
            refine ⟨9519619949546191448091991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50771306397579687723157285 9519619949546191448091991)
            ·
              refine ⟨14279429924319287172137987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9519619949546191448091991 14279429924319287172137987)
              ·
                refine ⟨21419144886478930758206981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14279429924319287172137987 21419144886478930758206981)
                ·
                  refine ⟨4016089666214799517163809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21419144886478930758206981 4016089666214799517163809)
                  ·
                    refine ⟨3012067249661099637872857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4016089666214799517163809 3012067249661099637872857)
                    ·
                      refine ⟨2259050437245824728404643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3012067249661099637872857 2259050437245824728404643)
                      ·
                        rfl

theorem cell23_4399485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 4, 2, 2].length) (baseStart_4399485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4399485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4399485 prefixEnd_4399485 := by exact prefixLift 4399485
  have htrace : WordTrace (prefixWord ++ tailWord_4399485) baseStart_4399485 baseEnd_4399485 := by
    simpa [prefixWord, tailWord_4399485, baseEnd_4399485] using wordTrace_append hprefix tailTrace_4399485
  have hstable : (prefixWord ++ tailWord_4399485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4399485).length < 2 ^ (prefixWord ++ tailWord_4399485).sum := by decide
  have hdescent : baseEnd_4399485 < baseStart_4399485 := by decide
  rcases family_descends (prefixWord ++ tailWord_4399485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4399502 : List Nat := [4, 1, 1, 4, 1, 3, 1, 1, 1, 4, 2]
def baseStart_4399502 : Nat := 118140960795 + 4399502 * 2 ^ 59
def prefixEnd_4399502 : Nat := 4983230072969 + 3 ^ 40 * 4399502 * 2
def baseEnd_4399502 : Nat := 2259059166416951161892065

theorem tailTrace_4399502 : CollatzResearch.WordTrace tailWord_4399502 prefixEnd_4399502 2259059166416951161892065 := by
  unfold tailWord_4399502
  simp only [CollatzResearch.WordTrace]
  refine ⟨20057877563420387995835095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106975347004908735977787173 20057877563420387995835095)
  ·
    refine ⟨30086816345130581993752643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20057877563420387995835095 30086816345130581993752643)
    ·
      refine ⟨45130224517695872990628965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30086816345130581993752643 45130224517695872990628965)
      ·
        refine ⟨8461917097067976185742931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45130224517695872990628965 8461917097067976185742931)
        ·
          refine ⟨12692875645601964278614397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8461917097067976185742931 12692875645601964278614397)
          ·
            refine ⟨4759828367100736604480399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12692875645601964278614397 4759828367100736604480399)
            ·
              refine ⟨7139742550651104906720599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4759828367100736604480399 7139742550651104906720599)
              ·
                refine ⟨10709613825976657360080899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7139742550651104906720599 10709613825976657360080899)
                ·
                  refine ⟨16064420738964986040121349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10709613825976657360080899 16064420738964986040121349)
                  ·
                    refine ⟨3012078888555934882522753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16064420738964986040121349 3012078888555934882522753)
                    ·
                      refine ⟨2259059166416951161892065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3012078888555934882522753 2259059166416951161892065)
                      ·
                        rfl

theorem cell23_4399502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_4399502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4399502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4399502 prefixEnd_4399502 := by exact prefixLift 4399502
  have htrace : WordTrace (prefixWord ++ tailWord_4399502) baseStart_4399502 baseEnd_4399502 := by
    simpa [prefixWord, tailWord_4399502, baseEnd_4399502] using wordTrace_append hprefix tailTrace_4399502
  have hstable : (prefixWord ++ tailWord_4399502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4399502).length < 2 ^ (prefixWord ++ tailWord_4399502).sum := by decide
  have hdescent : baseEnd_4399502 < baseStart_4399502 := by decide
  rcases family_descends (prefixWord ++ tailWord_4399502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4399548 : List Nat := [2, 2, 2, 4, 1, 2, 1, 1, 1, 2, 5]
def baseStart_4399548 : Nat := 118140960795 + 4399548 * 2 ^ 59
def prefixEnd_4399548 : Nat := 4983230072969 + 3 ^ 40 * 4399548 * 2
def baseEnd_4399548 : Nat := 2259082786527057981916853

theorem tailTrace_4399548 : CollatzResearch.WordTrace tailWord_4399548 prefixEnd_4399548 2259082786527057981916853 := by
  unfold tailWord_4399548
  simp only [CollatzResearch.WordTrace]
  refine ⟨80232349132598226911427649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106976465510130969215236865 80232349132598226911427649)
  ·
    refine ⟨60174261849448670183570737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80232349132598226911427649 60174261849448670183570737)
    ·
      refine ⟨45130696387086502637678053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60174261849448670183570737 45130696387086502637678053)
      ·
        refine ⟨8462005572578719244564635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45130696387086502637678053 8462005572578719244564635)
        ·
          refine ⟨12693008358868078866846953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8462005572578719244564635 12693008358868078866846953)
          ·
            refine ⟨9519756269151059150135215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12693008358868078866846953 9519756269151059150135215)
            ·
              refine ⟨14279634403726588725202823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9519756269151059150135215 14279634403726588725202823)
              ·
                refine ⟨21419451605589883087804235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14279634403726588725202823 21419451605589883087804235)
                ·
                  refine ⟨32129177408384824631706353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21419451605589883087804235 32129177408384824631706353)
                  ·
                    refine ⟨24096883056288618473779765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32129177408384824631706353 24096883056288618473779765)
                    ·
                      refine ⟨2259082786527057981916853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24096883056288618473779765 2259082786527057981916853)
                      ·
                        rfl

theorem cell23_4399548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_4399548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4399548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4399548 prefixEnd_4399548 := by exact prefixLift 4399548
  have htrace : WordTrace (prefixWord ++ tailWord_4399548) baseStart_4399548 baseEnd_4399548 := by
    simpa [prefixWord, tailWord_4399548, baseEnd_4399548] using wordTrace_append hprefix tailTrace_4399548
  have hstable : (prefixWord ++ tailWord_4399548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4399548).length < 2 ^ (prefixWord ++ tailWord_4399548).sum := by decide
  have hdescent : baseEnd_4399548 < baseStart_4399548 := by decide
  rcases family_descends (prefixWord ++ tailWord_4399548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4399561 : List Nat := [1, 2, 1, 1, 2, 1, 4, 1, 3, 4, 3]
def baseStart_4399561 : Nat := 118140960795 + 4399561 * 2 ^ 59
def prefixEnd_4399561 : Nat := 4983230072969 + 3 ^ 40 * 4399561 * 2
def baseEnd_4399561 : Nat := 2259089461775566431054293

theorem tailTrace_4399561 : CollatzResearch.WordTrace tailWord_4399561 prefixEnd_4399561 2259089461775566431054293 := by
  unfold tailWord_4399561
  simp only [CollatzResearch.WordTrace]
  refine ⟨160465172414149357043078537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106976781609432904695385691 160465172414149357043078537)
  ·
    refine ⟨120348879310612017782308903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160465172414149357043078537 120348879310612017782308903)
    ·
      refine ⟨180523318965918026673463355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120348879310612017782308903 180523318965918026673463355)
      ·
        refine ⟨270784978448877040010195033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180523318965918026673463355 270784978448877040010195033)
        ·
          refine ⟨203088733836657780007646275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 270784978448877040010195033 203088733836657780007646275)
          ·
            refine ⟨304633100754986670011469413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203088733836657780007646275 304633100754986670011469413)
            ·
              refine ⟨57118706391560000627150515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 304633100754986670011469413 57118706391560000627150515)
              ·
                refine ⟨85678059587340000940725773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57118706391560000627150515 85678059587340000940725773)
                ·
                  refine ⟨32129272345252500352772165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 85678059587340000940725773 32129272345252500352772165)
                  ·
                    refine ⟨6024238564734843816144781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32129272345252500352772165 6024238564734843816144781)
                    ·
                      refine ⟨2259089461775566431054293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6024238564734843816144781 2259089461775566431054293)
                      ·
                        rfl

theorem cell23_4399561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 4, 3].length) (baseStart_4399561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4399561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4399561 prefixEnd_4399561 := by exact prefixLift 4399561
  have htrace : WordTrace (prefixWord ++ tailWord_4399561) baseStart_4399561 baseEnd_4399561 := by
    simpa [prefixWord, tailWord_4399561, baseEnd_4399561] using wordTrace_append hprefix tailTrace_4399561
  have hstable : (prefixWord ++ tailWord_4399561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4399561).length < 2 ^ (prefixWord ++ tailWord_4399561).sum := by decide
  have hdescent : baseEnd_4399561 < baseStart_4399561 := by decide
  rcases family_descends (prefixWord ++ tailWord_4399561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4399585 : List Nat := [1, 2, 3, 1, 2, 2, 2, 5, 1, 4]
def baseStart_4399585 : Nat := 118140960795 + 4399585 * 2 ^ 59
def prefixEnd_4399585 : Nat := 4983230072969 + 3 ^ 40 * 4399585 * 2
def baseEnd_4399585 : Nat := 753033928437091445718061

theorem tailTrace_4399585 : CollatzResearch.WordTrace tailWord_4399585 prefixEnd_4399585 753033928437091445718061 := by
  unfold tailWord_4399585
  simp only [CollatzResearch.WordTrace]
  refine ⟨160466047766062409141952209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106977365177374939427968139 160466047766062409141952209)
  ·
    refine ⟨120349535824546806856464157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160466047766062409141952209 120349535824546806856464157)
    ·
      refine ⟨45131075934205052571174059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120349535824546806856464157 45131075934205052571174059)
      ·
        refine ⟨67696613901307578856761089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45131075934205052571174059 67696613901307578856761089)
        ·
          refine ⟨50772460425980684142570817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67696613901307578856761089 50772460425980684142570817)
          ·
            refine ⟨38079345319485513106928113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50772460425980684142570817 38079345319485513106928113)
            ·
              refine ⟨28559508989614134830196085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38079345319485513106928113 28559508989614134830196085)
              ·
                refine ⟨2677453967776325140330883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28559508989614134830196085 2677453967776325140330883)
                ·
                  refine ⟨4016180951664487710496325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2677453967776325140330883 4016180951664487710496325)
                  ·
                    refine ⟨753033928437091445718061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4016180951664487710496325 753033928437091445718061)
                    ·
                      rfl

theorem cell23_4399585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 5, 1, 4].length) (baseStart_4399585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4399585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4399585 prefixEnd_4399585 := by exact prefixLift 4399585
  have htrace : WordTrace (prefixWord ++ tailWord_4399585) baseStart_4399585 baseEnd_4399585 := by
    simpa [prefixWord, tailWord_4399585, baseEnd_4399585] using wordTrace_append hprefix tailTrace_4399585
  have hstable : (prefixWord ++ tailWord_4399585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4399585).length < 2 ^ (prefixWord ++ tailWord_4399585).sum := by decide
  have hdescent : baseEnd_4399585 < baseStart_4399585 := by decide
  rcases family_descends (prefixWord ++ tailWord_4399585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4399598 : List Nat := [4, 1, 2, 1, 2, 2, 1, 4, 6]
def baseStart_4399598 : Nat := 118140960795 + 4399598 * 2 ^ 59
def prefixEnd_4399598 : Nat := 4983230072969 + 3 ^ 40 * 4399598 * 2
def baseEnd_4399598 : Nat := 251012051173309198476847

theorem tailTrace_4399598 : CollatzResearch.WordTrace tailWord_4399598 prefixEnd_4399598 251012051173309198476847 := by
  unfold tailWord_4399598
  simp only [CollatzResearch.WordTrace]
  refine ⟨20058315239376914045271931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106977681276676874908116965 20058315239376914045271931)
  ·
    refine ⟨30087472859065371067907897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20058315239376914045271931 30087472859065371067907897)
    ·
      refine ⟨22565604644299028300930923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30087472859065371067907897 22565604644299028300930923)
      ·
        refine ⟨33848406966448542451396385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22565604644299028300930923 33848406966448542451396385)
        ·
          refine ⟨25386305224836406838547289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33848406966448542451396385 25386305224836406838547289)
          ·
            refine ⟨19039728918627305128910467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25386305224836406838547289 19039728918627305128910467)
            ·
              refine ⟨28559593377940957693365701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19039728918627305128910467 28559593377940957693365701)
              ·
                refine ⟨5354923758363929567506069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28559593377940957693365701 5354923758363929567506069)
                ·
                  refine ⟨251012051173309198476847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5354923758363929567506069 251012051173309198476847)
                  ·
                    rfl

theorem cell23_4399598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 4, 6].length) (baseStart_4399598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4399598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4399598 prefixEnd_4399598 := by exact prefixLift 4399598
  have htrace : WordTrace (prefixWord ++ tailWord_4399598) baseStart_4399598 baseEnd_4399598 := by
    simpa [prefixWord, tailWord_4399598, baseEnd_4399598] using wordTrace_append hprefix tailTrace_4399598
  have hstable : (prefixWord ++ tailWord_4399598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4399598).length < 2 ^ (prefixWord ++ tailWord_4399598).sum := by decide
  have hdescent : baseEnd_4399598 < baseStart_4399598 := by decide
  rcases family_descends (prefixWord ++ tailWord_4399598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4399601 : List Nat := [1, 2, 2, 2, 3, 1, 2, 1, 1, 2, 6]
def baseStart_4399601 : Nat := 118140960795 + 4399601 * 2 ^ 59
def prefixEnd_4399601 : Nat := 4983230072969 + 3 ^ 40 * 4399601 * 2
def baseEnd_4399601 : Nat := 2259110001001746274554109

theorem tailTrace_4399601 : CollatzResearch.WordTrace tailWord_4399601 prefixEnd_4399601 2259110001001746274554109 := by
  unfold tailWord_4399601
  simp only [CollatzResearch.WordTrace]
  refine ⟨160466631334004443874534657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106977754222669629249689771 160466631334004443874534657)
  ·
    refine ⟨120349973500503332905900993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160466631334004443874534657 120349973500503332905900993)
    ·
      refine ⟨90262480125377499679425745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120349973500503332905900993 90262480125377499679425745)
      ·
        refine ⟨67696860094033124759569309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90262480125377499679425745 67696860094033124759569309)
        ·
          refine ⟨25386322535262421784838491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67696860094033124759569309 25386322535262421784838491)
          ·
            refine ⟨38079483802893632677257737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25386322535262421784838491 38079483802893632677257737)
            ·
              refine ⟨28559612852170224507943303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38079483802893632677257737 28559612852170224507943303)
              ·
                refine ⟨42839419278255336761914955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28559612852170224507943303 42839419278255336761914955)
                ·
                  refine ⟨64259128917383005142872433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42839419278255336761914955 64259128917383005142872433)
                  ·
                    refine ⟨48194346688037253857154325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 64259128917383005142872433 48194346688037253857154325)
                    ·
                      refine ⟨2259110001001746274554109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48194346688037253857154325 2259110001001746274554109)
                      ·
                        rfl

theorem cell23_4399601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_4399601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4399601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4399601 prefixEnd_4399601 := by exact prefixLift 4399601
  have htrace : WordTrace (prefixWord ++ tailWord_4399601) baseStart_4399601 baseEnd_4399601 := by
    simpa [prefixWord, tailWord_4399601, baseEnd_4399601] using wordTrace_append hprefix tailTrace_4399601
  have hstable : (prefixWord ++ tailWord_4399601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4399601).length < 2 ^ (prefixWord ++ tailWord_4399601).sum := by decide
  have hdescent : baseEnd_4399601 < baseStart_4399601 := by decide
  rcases family_descends (prefixWord ++ tailWord_4399601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4399628 : List Nat := [2, 2, 1, 2, 4, 1, 2, 1, 3, 5]
def baseStart_4399628 : Nat := 118140960795 + 4399628 * 2 ^ 59
def prefixEnd_4399628 : Nat := 4983230072969 + 3 ^ 40 * 4399628 * 2
def baseEnd_4399628 : Nat := 753041288326472556305495

theorem tailTrace_4399628 : CollatzResearch.WordTrace tailWord_4399628 prefixEnd_4399628 753041288326472556305495 := by
  unfold tailWord_4399628
  simp only [CollatzResearch.WordTrace]
  refine ⟨80233808052453313742883769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106978410736604418323845025 80233808052453313742883769)
  ·
    refine ⟨60175356039339985307162827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80233808052453313742883769 60175356039339985307162827)
    ·
      refine ⟨90263034059009977960744241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60175356039339985307162827 90263034059009977960744241)
      ·
        refine ⟨67697275544257483470558181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90263034059009977960744241 67697275544257483470558181)
        ·
          refine ⟨12693239164548278150729659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67697275544257483470558181 12693239164548278150729659)
          ·
            refine ⟨19039858746822417226094489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12693239164548278150729659 19039858746822417226094489)
            ·
              refine ⟨14279894060116812919570867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19039858746822417226094489 14279894060116812919570867)
              ·
                refine ⟨21419841090175219379356301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14279894060116812919570867 21419841090175219379356301)
                ·
                  refine ⟨8032440408815707267258613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21419841090175219379356301 8032440408815707267258613)
                  ·
                    refine ⟨753041288326472556305495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8032440408815707267258613 753041288326472556305495)
                    ·
                      rfl

theorem cell23_4399628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 3, 5].length) (baseStart_4399628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4399628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4399628 prefixEnd_4399628 := by exact prefixLift 4399628
  have htrace : WordTrace (prefixWord ++ tailWord_4399628) baseStart_4399628 baseEnd_4399628 := by
    simpa [prefixWord, tailWord_4399628, baseEnd_4399628] using wordTrace_append hprefix tailTrace_4399628
  have hstable : (prefixWord ++ tailWord_4399628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4399628).length < 2 ^ (prefixWord ++ tailWord_4399628).sum := by decide
  have hdescent : baseEnd_4399628 < baseStart_4399628 := by decide
  rcases family_descends (prefixWord ++ tailWord_4399628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4399629 : List Nat := [1, 7, 1, 1, 1, 1, 3, 1, 2, 2, 3]
def baseStart_4399629 : Nat := 118140960795 + 4399629 * 2 ^ 59
def prefixEnd_4399629 : Nat := 4983230072969 + 3 ^ 40 * 4399629 * 2
def baseEnd_4399629 : Nat := 2259124378460072165003981

theorem tailTrace_4399629 : CollatzResearch.WordTrace tailWord_4399629 prefixEnd_4399629 2259124378460072165003981 := by
  unfold tailWord_4399629
  simp only [CollatzResearch.WordTrace]
  refine ⟨160467652577903004656553941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106978435051935336437702627 160467652577903004656553941)
  ·
    refine ⟨3760960607294601671637983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 160467652577903004656553941 3760960607294601671637983)
    ·
      refine ⟨5641440910941902507456975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3760960607294601671637983 5641440910941902507456975)
      ·
        refine ⟨8462161366412853761185463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5641440910941902507456975 8462161366412853761185463)
        ·
          refine ⟨12693242049619280641778195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8462161366412853761185463 12693242049619280641778195)
          ·
            refine ⟨19039863074428920962667293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12693242049619280641778195 19039863074428920962667293)
            ·
              refine ⟨7139948652910845361000235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19039863074428920962667293 7139948652910845361000235)
              ·
                refine ⟨10709922979366268041500353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7139948652910845361000235 10709922979366268041500353)
                ·
                  refine ⟨8032442234524701031125265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10709922979366268041500353 8032442234524701031125265)
                  ·
                    refine ⟨6024331675893525773343949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8032442234524701031125265 6024331675893525773343949)
                    ·
                      refine ⟨2259124378460072165003981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6024331675893525773343949 2259124378460072165003981)
                      ·
                        rfl

theorem cell23_4399629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_4399629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4399629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4399629 prefixEnd_4399629 := by exact prefixLift 4399629
  have htrace : WordTrace (prefixWord ++ tailWord_4399629) baseStart_4399629 baseEnd_4399629 := by
    simpa [prefixWord, tailWord_4399629, baseEnd_4399629] using wordTrace_append hprefix tailTrace_4399629
  have hstable : (prefixWord ++ tailWord_4399629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4399629).length < 2 ^ (prefixWord ++ tailWord_4399629).sum := by decide
  have hdescent : baseEnd_4399629 < baseStart_4399629 := by decide
  rcases family_descends (prefixWord ++ tailWord_4399629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4399642 : List Nat := [3, 1, 1, 3, 1, 1, 3, 5, 1, 1, 3]
def baseStart_4399642 : Nat := 118140960795 + 4399642 * 2 ^ 59
def prefixEnd_4399642 : Nat := 4983230072969 + 3 ^ 40 * 4399642 * 2
def baseEnd_4399642 : Nat := 2259131053708580614141421

theorem tailTrace_4399642 : CollatzResearch.WordTrace tailWord_4399642 prefixEnd_4399642 2259131053708580614141421 := by
  unfold tailWord_4399642
  simp only [CollatzResearch.WordTrace]
  refine ⟨40117031681713976969194295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106978751151237271917851453 40117031681713976969194295)
  ·
    refine ⟨60175547522570965453791443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40117031681713976969194295 60175547522570965453791443)
    ·
      refine ⟨90263321283856448180687165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60175547522570965453791443 90263321283856448180687165)
      ·
        refine ⟨33848745481446168067757687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90263321283856448180687165 33848745481446168067757687)
        ·
          refine ⟨50773118222169252101636531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33848745481446168067757687 50773118222169252101636531)
          ·
            refine ⟨76159677333253878152454797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50773118222169252101636531 76159677333253878152454797)
            ·
              refine ⟨28559878999970204307170549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76159677333253878152454797 28559878999970204307170549)
              ·
                refine ⟨2677488656247206653797239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28559878999970204307170549 2677488656247206653797239)
                ·
                  refine ⟨4016232984370809980695859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2677488656247206653797239 4016232984370809980695859)
                  ·
                    refine ⟨6024349476556214971043789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4016232984370809980695859 6024349476556214971043789)
                    ·
                      refine ⟨2259131053708580614141421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6024349476556214971043789 2259131053708580614141421)
                      ·
                        rfl

theorem cell23_4399642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 5, 1, 1, 3].length) (baseStart_4399642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4399642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4399642 prefixEnd_4399642 := by exact prefixLift 4399642
  have htrace : WordTrace (prefixWord ++ tailWord_4399642) baseStart_4399642 baseEnd_4399642 := by
    simpa [prefixWord, tailWord_4399642, baseEnd_4399642] using wordTrace_append hprefix tailTrace_4399642
  have hstable : (prefixWord ++ tailWord_4399642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4399642).length < 2 ^ (prefixWord ++ tailWord_4399642).sum := by decide
  have hdescent : baseEnd_4399642 < baseStart_4399642 := by decide
  rcases family_descends (prefixWord ++ tailWord_4399642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4399645 : List Nat := [1, 4, 2, 2, 1, 3, 1, 3, 1, 5]
def baseStart_4399645 : Nat := 118140960795 + 4399645 * 2 ^ 59
def prefixEnd_4399645 : Nat := 4983230072969 + 3 ^ 40 * 4399645 * 2
def baseEnd_4399645 : Nat := 753044198050181367467969

theorem tailTrace_4399645 : CollatzResearch.WordTrace tailWord_4399645 prefixEnd_4399645 753044198050181367467969 := by
  unfold tailWord_4399645
  simp only [CollatzResearch.WordTrace]
  refine ⟨160468236145845039389136389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106978824097230026259424259 160468236145845039389136389)
  ·
    refine ⟨30087794277345944885463073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 160468236145845039389136389 30087794277345944885463073)
    ·
      refine ⟨22565845708009458664097305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30087794277345944885463073 22565845708009458664097305)
      ·
        refine ⟨16924384281007093998072979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22565845708009458664097305 16924384281007093998072979)
        ·
          refine ⟨25386576421510640997109469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16924384281007093998072979 25386576421510640997109469)
          ·
            refine ⟨9519966158066490373916051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25386576421510640997109469 9519966158066490373916051)
            ·
              refine ⟨14279949237099735560874077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9519966158066490373916051 14279949237099735560874077)
              ·
                refine ⟨5354980963912400835327779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14279949237099735560874077 5354980963912400835327779)
                ·
                  refine ⟨8032471445868601252991669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5354980963912400835327779 8032471445868601252991669)
                  ·
                    refine ⟨753044198050181367467969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8032471445868601252991669 753044198050181367467969)
                    ·
                      rfl

theorem cell23_4399645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 3, 1, 5].length) (baseStart_4399645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4399645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4399645 prefixEnd_4399645 := by exact prefixLift 4399645
  have htrace : WordTrace (prefixWord ++ tailWord_4399645) baseStart_4399645 baseEnd_4399645 := by
    simpa [prefixWord, tailWord_4399645, baseEnd_4399645] using wordTrace_append hprefix tailTrace_4399645
  have hstable : (prefixWord ++ tailWord_4399645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4399645).length < 2 ^ (prefixWord ++ tailWord_4399645).sum := by decide
  have hdescent : baseEnd_4399645 < baseStart_4399645 := by decide
  rcases family_descends (prefixWord ++ tailWord_4399645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4399671 : List Nat := [1, 1, 3, 1, 2, 3, 2, 10]
def baseStart_4399671 : Nat := 118140960795 + 4399671 * 2 ^ 59
def prefixEnd_4399671 : Nat := 4983230072969 + 3 ^ 40 * 4399671 * 2
def baseEnd_4399671 : Nat := 83672072023983740765881

theorem tailTrace_4399671 : CollatzResearch.WordTrace tailWord_4399671 prefixEnd_4399671 83672072023983740765881 := by
  unfold tailWord_4399671
  simp only [CollatzResearch.WordTrace]
  refine ⟨160469184443750845829582867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106979456295833897219721911 160469184443750845829582867)
  ·
    refine ⟨240703776665626268744374301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160469184443750845829582867 240703776665626268744374301)
    ·
      refine ⟨90263916249609850779140363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 240703776665626268744374301 90263916249609850779140363)
      ·
        refine ⟨135395874374414776168710545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90263916249609850779140363 135395874374414776168710545)
        ·
          refine ⟨101546905780811082126532909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135395874374414776168710545 101546905780811082126532909)
          ·
            refine ⟨38080089667804155797449841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101546905780811082126532909 38080089667804155797449841)
            ·
              refine ⟨28560067250853116848087381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38080089667804155797449841 28560067250853116848087381)
              ·
                refine ⟨83672072023983740765881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 28560067250853116848087381 83672072023983740765881)
                ·
                  rfl

theorem cell23_4399671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 10].length) (baseStart_4399671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4399671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4399671 prefixEnd_4399671 := by exact prefixLift 4399671
  have htrace : WordTrace (prefixWord ++ tailWord_4399671) baseStart_4399671 baseEnd_4399671 := by
    simpa [prefixWord, tailWord_4399671, baseEnd_4399671] using wordTrace_append hprefix tailTrace_4399671
  have hstable : (prefixWord ++ tailWord_4399671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4399671).length < 2 ^ (prefixWord ++ tailWord_4399671).sum := by decide
  have hdescent : baseEnd_4399671 < baseStart_4399671 := by decide
  rcases family_descends (prefixWord ++ tailWord_4399671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4399685 : List Nat := [1, 3, 1, 1, 1, 5, 1, 4, 1, 2, 3]
def baseStart_4399685 : Nat := 118140960795 + 4399685 * 2 ^ 59
def prefixEnd_4399685 : Nat := 4983230072969 + 3 ^ 40 * 4399685 * 2
def baseEnd_4399685 : Nat := 2259153133376723945903723

theorem tailTrace_4399685 : CollatzResearch.WordTrace tailWord_4399685 prefixEnd_4399685 2259153133376723945903723 := by
  unfold tailWord_4399685
  simp only [CollatzResearch.WordTrace]
  refine ⟨160469695065700126220592509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106979796710466750813728339 160469695065700126220592509)
  ·
    refine ⟨60176135649637547332722191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160469695065700126220592509 60176135649637547332722191)
    ·
      refine ⟨90264203474456320999083287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60176135649637547332722191 90264203474456320999083287)
      ·
        refine ⟨135396305211684481498624931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90264203474456320999083287 135396305211684481498624931)
        ·
          refine ⟨203094457817526722247937397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135396305211684481498624931 203094457817526722247937397)
          ·
            refine ⟨19040105420393130210744131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 203094457817526722247937397 19040105420393130210744131)
            ·
              refine ⟨28560158130589695316116197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19040105420393130210744131 28560158130589695316116197)
              ·
                refine ⟨5355029649485567871771787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28560158130589695316116197 5355029649485567871771787)
                ·
                  refine ⟨8032544474228351807657681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5355029649485567871771787 8032544474228351807657681)
                  ·
                    refine ⟨6024408355671263855743261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8032544474228351807657681 6024408355671263855743261)
                    ·
                      refine ⟨2259153133376723945903723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6024408355671263855743261 2259153133376723945903723)
                      ·
                        rfl

theorem cell23_4399685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 4, 1, 2, 3].length) (baseStart_4399685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4399685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4399685 prefixEnd_4399685 := by exact prefixLift 4399685
  have htrace : WordTrace (prefixWord ++ tailWord_4399685) baseStart_4399685 baseEnd_4399685 := by
    simpa [prefixWord, tailWord_4399685, baseEnd_4399685] using wordTrace_append hprefix tailTrace_4399685
  have hstable : (prefixWord ++ tailWord_4399685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4399685).length < 2 ^ (prefixWord ++ tailWord_4399685).sum := by decide
  have hdescent : baseEnd_4399685 < baseStart_4399685 := by decide
  rcases family_descends (prefixWord ++ tailWord_4399685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4399710 : List Nat := [4, 4, 1, 2, 2, 1, 1, 1, 3, 1, 3]
def baseStart_4399710 : Nat := 118140960795 + 4399710 * 2 ^ 59
def prefixEnd_4399710 : Nat := 4983230072969 + 3 ^ 40 * 4399710 * 2
def baseEnd_4399710 : Nat := 2259165970393086348091109

theorem tailTrace_4399710 : CollatzResearch.WordTrace tailWord_4399710 prefixEnd_4399710 2259165970393086348091109 := by
  unfold tailWord_4399710
  simp only [CollatzResearch.WordTrace]
  refine ⟨20058825861326194436281573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106980404593739703660168389 20058825861326194436281573)
  ·
    refine ⟨3761029848998661456802795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20058825861326194436281573 3761029848998661456802795)
    ·
      refine ⟨5641544773497992185204193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3761029848998661456802795 5641544773497992185204193)
      ·
        refine ⟨4231158580123494138903145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5641544773497992185204193 4231158580123494138903145)
        ·
          refine ⟨3173368935092620604177359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4231158580123494138903145 3173368935092620604177359)
          ·
            refine ⟨4760053402638930906266039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3173368935092620604177359 4760053402638930906266039)
            ·
              refine ⟨7140080103958396359399059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4760053402638930906266039 7140080103958396359399059)
              ·
                refine ⟨10710120155937594539098589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7140080103958396359399059 10710120155937594539098589)
                ·
                  refine ⟨4016295058476597952161971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10710120155937594539098589 4016295058476597952161971)
                  ·
                    refine ⟨6024442587714896928242957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4016295058476597952161971 6024442587714896928242957)
                    ·
                      refine ⟨2259165970393086348091109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6024442587714896928242957 2259165970393086348091109)
                      ·
                        rfl

theorem cell23_4399710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_4399710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4399710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4399710 prefixEnd_4399710 := by exact prefixLift 4399710
  have htrace : WordTrace (prefixWord ++ tailWord_4399710) baseStart_4399710 baseEnd_4399710 := by
    simpa [prefixWord, tailWord_4399710, baseEnd_4399710] using wordTrace_append hprefix tailTrace_4399710
  have hstable : (prefixWord ++ tailWord_4399710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4399710).length < 2 ^ (prefixWord ++ tailWord_4399710).sum := by decide
  have hdescent : baseEnd_4399710 < baseStart_4399710 := by decide
  rcases family_descends (prefixWord ++ tailWord_4399710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4399715 : List Nat := [1, 1, 1, 5, 1, 2, 1, 3, 4, 1, 3]
def baseStart_4399715 : Nat := 118140960795 + 4399715 * 2 ^ 59
def prefixEnd_4399715 : Nat := 4983230072969 + 3 ^ 40 * 4399715 * 2
def baseEnd_4399715 : Nat := 2259168537796358828528585

theorem tailTrace_4399715 : CollatzResearch.WordTrace tailWord_4399715 prefixEnd_4399715 2259168537796358828528585 := by
  unfold tailWord_4399715
  simp only [CollatzResearch.WordTrace]
  refine ⟨160470789255591441344184599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106980526170394294229456399 160470789255591441344184599)
  ·
    refine ⟨240706183883387162016276899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160470789255591441344184599 240706183883387162016276899)
    ·
      refine ⟨361059275825080743024415349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240706183883387162016276899 361059275825080743024415349)
      ·
        refine ⟨33849307108601319658538939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 361059275825080743024415349 33849307108601319658538939)
        ·
          refine ⟨50773960662901979487808409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33849307108601319658538939 50773960662901979487808409)
          ·
            refine ⟨38080470497176484615856307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50773960662901979487808409 38080470497176484615856307)
            ·
              refine ⟨57120705745764726923784461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38080470497176484615856307 57120705745764726923784461)
              ·
                refine ⟨21420264654661772596419173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57120705745764726923784461 21420264654661772596419173)
                ·
                  refine ⟨4016299622749082361828595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21420264654661772596419173 4016299622749082361828595)
                  ·
                    refine ⟨6024449434123623542742893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4016299622749082361828595 6024449434123623542742893)
                    ·
                      refine ⟨2259168537796358828528585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6024449434123623542742893 2259168537796358828528585)
                      ·
                        rfl

theorem cell23_4399715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 4, 1, 3].length) (baseStart_4399715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4399715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4399715 prefixEnd_4399715 := by exact prefixLift 4399715
  have htrace : WordTrace (prefixWord ++ tailWord_4399715) baseStart_4399715 baseEnd_4399715 := by
    simpa [prefixWord, tailWord_4399715, baseEnd_4399715] using wordTrace_append hprefix tailTrace_4399715
  have hstable : (prefixWord ++ tailWord_4399715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4399715).length < 2 ^ (prefixWord ++ tailWord_4399715).sum := by decide
  have hdescent : baseEnd_4399715 < baseStart_4399715 := by decide
  rcases family_descends (prefixWord ++ tailWord_4399715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4399716 : List Nat := [2, 3, 1, 1, 2, 2, 5, 2, 1, 2, 2]
def baseStart_4399716 : Nat := 118140960795 + 4399716 * 2 ^ 59
def prefixEnd_4399716 : Nat := 4983230072969 + 3 ^ 40 * 4399716 * 2
def baseEnd_4399716 : Nat := 2259169051277013324616081

theorem tailTrace_4399716 : CollatzResearch.WordTrace tailWord_4399716 prefixEnd_4399716 2259169051277013324616081 := by
  unfold tailWord_4399716
  simp only [CollatzResearch.WordTrace]
  refine ⟨80235412864293909257485501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106980550485725212343314001 80235412864293909257485501)
  ·
    refine ⟨30088279824110215971557063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80235412864293909257485501 30088279824110215971557063)
    ·
      refine ⟨45132419736165323957335595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30088279824110215971557063 45132419736165323957335595)
      ·
        refine ⟨67698629604247985936003393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45132419736165323957335595 67698629604247985936003393)
        ·
          refine ⟨50773972203185989452002545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67698629604247985936003393 50773972203185989452002545)
          ·
            refine ⟨38080479152389492089001909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50773972203185989452002545 38080479152389492089001909)
            ·
              refine ⟨3570044920536514883343929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38080479152389492089001909 3570044920536514883343929)
              ·
                refine ⟨2677533690402386162507947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3570044920536514883343929 2677533690402386162507947)
                ·
                  refine ⟨4016300535603579243761921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2677533690402386162507947 4016300535603579243761921)
                  ·
                    refine ⟨3012225401702684432821441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4016300535603579243761921 3012225401702684432821441)
                    ·
                      refine ⟨2259169051277013324616081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3012225401702684432821441 2259169051277013324616081)
                      ·
                        rfl

theorem cell23_4399716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 5, 2, 1, 2, 2].length) (baseStart_4399716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4399716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4399716 prefixEnd_4399716 := by exact prefixLift 4399716
  have htrace : WordTrace (prefixWord ++ tailWord_4399716) baseStart_4399716 baseEnd_4399716 := by
    simpa [prefixWord, tailWord_4399716, baseEnd_4399716] using wordTrace_append hprefix tailTrace_4399716
  have hstable : (prefixWord ++ tailWord_4399716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4399716).length < 2 ^ (prefixWord ++ tailWord_4399716).sum := by decide
  have hdescent : baseEnd_4399716 < baseStart_4399716 := by decide
  rcases family_descends (prefixWord ++ tailWord_4399716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4399746 : List Nat := [3, 4, 3, 1, 1, 1, 1, 2, 1, 2, 4]
def baseStart_4399746 : Nat := 118140960795 + 4399746 * 2 ^ 59
def prefixEnd_4399746 : Nat := 4983230072969 + 3 ^ 40 * 4399746 * 2
def baseEnd_4399746 : Nat := 2259184455696648207240943

theorem tailTrace_4399746 : CollatzResearch.WordTrace tailWord_4399746 prefixEnd_4399746 2259184455696648207240943 := by
  unfold tailWord_4399746
  simp only [CollatzResearch.WordTrace]
  refine ⟨40117979979619783409640773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106981279945652755759042061 40117979979619783409640773)
  ·
    refine ⟨7522121246178709389307645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40117979979619783409640773 7522121246178709389307645)
    ·
      refine ⟨2820795467317016020990367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7522121246178709389307645 2820795467317016020990367)
      ·
        refine ⟨4231193200975524031485551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2820795467317016020990367 4231193200975524031485551)
        ·
          refine ⟨6346789801463286047228327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4231193200975524031485551 6346789801463286047228327)
          ·
            refine ⟨9520184702194929070842491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6346789801463286047228327 9520184702194929070842491)
            ·
              refine ⟨14280277053292393606263737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9520184702194929070842491 14280277053292393606263737)
              ·
                refine ⟨10710207789969295204697803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14280277053292393606263737 10710207789969295204697803)
                ·
                  refine ⟨16065311684953942807046705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10710207789969295204697803 16065311684953942807046705)
                  ·
                    refine ⟨12048983763715457105285029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16065311684953942807046705 12048983763715457105285029)
                    ·
                      refine ⟨2259184455696648207240943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12048983763715457105285029 2259184455696648207240943)
                      ·
                        rfl

theorem cell23_4399746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_4399746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4399746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4399746 prefixEnd_4399746 := by exact prefixLift 4399746
  have htrace : WordTrace (prefixWord ++ tailWord_4399746) baseStart_4399746 baseEnd_4399746 := by
    simpa [prefixWord, tailWord_4399746, baseEnd_4399746] using wordTrace_append hprefix tailTrace_4399746
  have hstable : (prefixWord ++ tailWord_4399746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4399746).length < 2 ^ (prefixWord ++ tailWord_4399746).sum := by decide
  have hdescent : baseEnd_4399746 < baseStart_4399746 := by decide
  rcases family_descends (prefixWord ++ tailWord_4399746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4399789 : List Nat := [1, 5, 2, 1, 1, 3, 2, 1, 1, 4, 2]
def baseStart_4399789 : Nat := 118140960795 + 4399789 * 2 ^ 59
def prefixEnd_4399789 : Nat := 4983230072969 + 3 ^ 40 * 4399789 * 2
def baseEnd_4399789 : Nat := 2259206535364791539003245

theorem tailTrace_4399789 : CollatzResearch.WordTrace tailWord_4399789 prefixEnd_4399789 2259206535364791539003245 := by
  unfold tailWord_4399789
  simp only [CollatzResearch.WordTrace]
  refine ⟨160473488257323351982378421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106982325504882234654918947 160473488257323351982378421)
  ·
    refine ⟨15044389524124064248347977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 160473488257323351982378421 15044389524124064248347977)
    ·
      refine ⟨11283292143093048186260983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15044389524124064248347977 11283292143093048186260983)
      ·
        refine ⟨16924938214639572279391475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11283292143093048186260983 16924938214639572279391475)
        ·
          refine ⟨25387407321959358419087213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16924938214639572279391475 25387407321959358419087213)
          ·
            refine ⟨9520277745734759407157705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25387407321959358419087213 9520277745734759407157705)
            ·
              refine ⟨7140208309301069555368279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9520277745734759407157705 7140208309301069555368279)
              ·
                refine ⟨10710312463951604333052419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7140208309301069555368279 10710312463951604333052419)
                ·
                  refine ⟨16065468695927406499578629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10710312463951604333052419 16065468695927406499578629)
                  ·
                    refine ⟨3012275380486388718670993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16065468695927406499578629 3012275380486388718670993)
                    ·
                      refine ⟨2259206535364791539003245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3012275380486388718670993 2259206535364791539003245)
                      ·
                        rfl

theorem cell23_4399789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 1, 1, 4, 2].length) (baseStart_4399789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4399789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4399789 prefixEnd_4399789 := by exact prefixLift 4399789
  have htrace : WordTrace (prefixWord ++ tailWord_4399789) baseStart_4399789 baseEnd_4399789 := by
    simpa [prefixWord, tailWord_4399789, baseEnd_4399789] using wordTrace_append hprefix tailTrace_4399789
  have hstable : (prefixWord ++ tailWord_4399789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4399789).length < 2 ^ (prefixWord ++ tailWord_4399789).sum := by decide
  have hdescent : baseEnd_4399789 < baseStart_4399789 := by decide
  rcases family_descends (prefixWord ++ tailWord_4399789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4399812 : List Nat := [2, 3, 3, 1, 1, 2, 1, 5, 5]
def baseStart_4399812 : Nat := 118140960795 + 4399812 * 2 ^ 59
def prefixEnd_4399812 : Nat := 4983230072969 + 3 ^ 40 * 4399812 * 2
def baseEnd_4399812 : Nat := 251024260602204994335071

theorem tailTrace_4399812 : CollatzResearch.WordTrace tailWord_4399812 prefixEnd_4399812 251024260602204994335071 := by
  unfold tailWord_4399812
  simp only [CollatzResearch.WordTrace]
  refine ⟨80237163568120013455232845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106982884757493351273643793 80237163568120013455232845)
  ·
    refine ⟨30088936338045005045712317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80237163568120013455232845 30088936338045005045712317)
    ·
      refine ⟨11283351126766876892142119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30088936338045005045712317 11283351126766876892142119)
      ·
        refine ⟨16925026690150315338213179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11283351126766876892142119 16925026690150315338213179)
        ·
          refine ⟨25387540035225473007319769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16925026690150315338213179 25387540035225473007319769)
          ·
            refine ⟨19040655026419104755489827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25387540035225473007319769 19040655026419104755489827)
            ·
              refine ⟨28560982539628657133234741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19040655026419104755489827 28560982539628657133234741)
              ·
                refine ⟨2677592113090186606240757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28560982539628657133234741 2677592113090186606240757)
                ·
                  refine ⟨251024260602204994335071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2677592113090186606240757 251024260602204994335071)
                  ·
                    rfl

theorem cell23_4399812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 5, 5].length) (baseStart_4399812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4399812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4399812 prefixEnd_4399812 := by exact prefixLift 4399812
  have htrace : WordTrace (prefixWord ++ tailWord_4399812) baseStart_4399812 baseEnd_4399812 := by
    simpa [prefixWord, tailWord_4399812, baseEnd_4399812] using wordTrace_append hprefix tailTrace_4399812
  have hstable : (prefixWord ++ tailWord_4399812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4399812).length < 2 ^ (prefixWord ++ tailWord_4399812).sum := by decide
  have hdescent : baseEnd_4399812 < baseStart_4399812 := by decide
  rcases family_descends (prefixWord ++ tailWord_4399812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4399815 : List Nat := [1, 1, 4, 1, 1, 1, 2, 2, 1, 7, 2]
def baseStart_4399815 : Nat := 118140960795 + 4399815 * 2 ^ 59
def prefixEnd_4399815 : Nat := 4983230072969 + 3 ^ 40 * 4399815 * 2
def baseEnd_4399815 : Nat := 2259219885861808437278125

theorem tailTrace_4399815 : CollatzResearch.WordTrace tailWord_4399815 prefixEnd_4399815 2259219885861808437278125 := by
  unfold tailWord_4399815
  simp only [CollatzResearch.WordTrace]
  refine ⟨160474436555229158422824899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106982957703486105615216599 160474436555229158422824899)
  ·
    refine ⟨240711654832843737634237349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160474436555229158422824899 240711654832843737634237349)
    ·
      refine ⟨45133435281158200806419503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 240711654832843737634237349 45133435281158200806419503)
      ·
        refine ⟨67700152921737301209629255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45133435281158200806419503 67700152921737301209629255)
        ·
          refine ⟨101550229382605951814443883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67700152921737301209629255 101550229382605951814443883)
          ·
            refine ⟨152325344073908927721665825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101550229382605951814443883 152325344073908927721665825)
            ·
              refine ⟨114244008055431695791249369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152325344073908927721665825 114244008055431695791249369)
              ·
                refine ⟨85683006041573771843437027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114244008055431695791249369 85683006041573771843437027)
                ·
                  refine ⟨128524509062360657765155541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85683006041573771843437027 128524509062360657765155541)
                  ·
                    refine ⟨3012293181149077916370833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 128524509062360657765155541 3012293181149077916370833)
                    ·
                      refine ⟨2259219885861808437278125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3012293181149077916370833 2259219885861808437278125)
                      ·
                        rfl

theorem cell23_4399815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 7, 2].length) (baseStart_4399815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4399815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4399815 prefixEnd_4399815 := by exact prefixLift 4399815
  have htrace : WordTrace (prefixWord ++ tailWord_4399815) baseStart_4399815 baseEnd_4399815 := by
    simpa [prefixWord, tailWord_4399815, baseEnd_4399815] using wordTrace_append hprefix tailTrace_4399815
  have hstable : (prefixWord ++ tailWord_4399815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4399815).length < 2 ^ (prefixWord ++ tailWord_4399815).sum := by decide
  have hdescent : baseEnd_4399815 < baseStart_4399815 := by decide
  rcases family_descends (prefixWord ++ tailWord_4399815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4399845 : List Nat := [1, 3, 1, 4, 1, 2, 1, 2, 1, 3, 4]
def baseStart_4399845 : Nat := 118140960795 + 4399845 * 2 ^ 59
def prefixEnd_4399845 : Nat := 4983230072969 + 3 ^ 40 * 4399845 * 2
def baseEnd_4399845 : Nat := 2259235290281443319902987

theorem tailTrace_4399845 : CollatzResearch.WordTrace tailWord_4399845 prefixEnd_4399845 2259235290281443319902987 := by
  unfold tailWord_4399845
  simp only [CollatzResearch.WordTrace]
  refine ⟨160475530745120473546416989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106983687163413649030944659 160475530745120473546416989)
  ·
    refine ⟨60178324029420177579906371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160475530745120473546416989 60178324029420177579906371)
    ·
      refine ⟨90267486044130266369859557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60178324029420177579906371 90267486044130266369859557)
      ·
        refine ⟨16925153633274424944348667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90267486044130266369859557 16925153633274424944348667)
        ·
          refine ⟨25387730449911637416523001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16925153633274424944348667 25387730449911637416523001)
          ·
            refine ⟨19040797837433728062392251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25387730449911637416523001 19040797837433728062392251)
            ·
              refine ⟨28561196756150592093588377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19040797837433728062392251 28561196756150592093588377)
              ·
                refine ⟨21420897567112944070191283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28561196756150592093588377 21420897567112944070191283)
                ·
                  refine ⟨32131346350669416105286925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21420897567112944070191283 32131346350669416105286925)
                  ·
                    refine ⟨12049254881501031039482597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32131346350669416105286925 12049254881501031039482597)
                    ·
                      refine ⟨2259235290281443319902987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12049254881501031039482597 2259235290281443319902987)
                      ·
                        rfl

theorem cell23_4399845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_4399845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4399845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4399845 prefixEnd_4399845 := by exact prefixLift 4399845
  have htrace : WordTrace (prefixWord ++ tailWord_4399845) baseStart_4399845 baseEnd_4399845 := by
    simpa [prefixWord, tailWord_4399845, baseEnd_4399845] using wordTrace_append hprefix tailTrace_4399845
  have hstable : (prefixWord ++ tailWord_4399845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4399845).length < 2 ^ (prefixWord ++ tailWord_4399845).sum := by decide
  have hdescent : baseEnd_4399845 < baseStart_4399845 := by decide
  rcases family_descends (prefixWord ++ tailWord_4399845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4399862 : List Nat := [5, 1, 1, 1, 1, 2, 2, 3, 2, 1, 4]
def baseStart_4399862 : Nat := 118140960795 + 4399862 * 2 ^ 59
def prefixEnd_4399862 : Nat := 4983230072969 + 3 ^ 40 * 4399862 * 2
def baseEnd_4399862 : Nat := 2259244019452569753390409

theorem tailTrace_4399862 : CollatzResearch.WordTrace tailWord_4399862 prefixEnd_4399862 2259244019452569753390409 := by
  unfold tailWord_4399862
  simp only [CollatzResearch.WordTrace]
  refine ⟨10029759424128680340611615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 106984100524039256966523893 10029759424128680340611615)
  ·
    refine ⟨15044639136193020510917423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10029759424128680340611615 15044639136193020510917423)
    ·
      refine ⟨22566958704289530766376135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15044639136193020510917423 22566958704289530766376135)
      ·
        refine ⟨33850438056434296149564203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22566958704289530766376135 33850438056434296149564203)
        ·
          refine ⟨50775657084651444224346305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33850438056434296149564203 50775657084651444224346305)
          ·
            refine ⟨38081742813488583168259729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50775657084651444224346305 38081742813488583168259729)
            ·
              refine ⟨28561307110116437376194797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38081742813488583168259729 28561307110116437376194797)
              ·
                refine ⟨10710490166293664016073049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28561307110116437376194797 10710490166293664016073049)
                ·
                  refine ⟨8032867624720248012054787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10710490166293664016073049 8032867624720248012054787)
                  ·
                    refine ⟨12049301437080372018082181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8032867624720248012054787 12049301437080372018082181)
                    ·
                      refine ⟨2259244019452569753390409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12049301437080372018082181 2259244019452569753390409)
                      ·
                        rfl

theorem cell23_4399862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_4399862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4399862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4399862 prefixEnd_4399862 := by exact prefixLift 4399862
  have htrace : WordTrace (prefixWord ++ tailWord_4399862) baseStart_4399862 baseEnd_4399862 := by
    simpa [prefixWord, tailWord_4399862, baseEnd_4399862] using wordTrace_append hprefix tailTrace_4399862
  have hstable : (prefixWord ++ tailWord_4399862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4399862).length < 2 ^ (prefixWord ++ tailWord_4399862).sum := by decide
  have hdescent : baseEnd_4399862 < baseStart_4399862 := by decide
  rcases family_descends (prefixWord ++ tailWord_4399862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4399865 : List Nat := [1, 2, 1, 3, 1, 1, 1, 2, 6, 2, 3]
def baseStart_4399865 : Nat := 118140960795 + 4399865 * 2 ^ 59
def prefixEnd_4399865 : Nat := 4983230072969 + 3 ^ 40 * 4399865 * 2
def baseEnd_4399865 : Nat := 2259245559894533241652895

theorem tailTrace_4399865 : CollatzResearch.WordTrace tailWord_4399865 prefixEnd_4399865 2259245559894533241652895 := by
  unfold tailWord_4399865
  simp only [CollatzResearch.WordTrace]
  refine ⟨160476260205048016962145049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106984173470032011308096699 160476260205048016962145049)
  ·
    refine ⟨120357195153786012721608787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160476260205048016962145049 120357195153786012721608787)
    ·
      refine ⟨180535792730679019082413181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120357195153786012721608787 180535792730679019082413181)
      ·
        refine ⟨67700922274004632155904943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 180535792730679019082413181 67700922274004632155904943)
        ·
          refine ⟨101551383411006948233857415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67700922274004632155904943 101551383411006948233857415)
          ·
            refine ⟨152327075116510422350786123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101551383411006948233857415 152327075116510422350786123)
            ·
              refine ⟨228490612674765633526179185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152327075116510422350786123 228490612674765633526179185)
              ·
                refine ⟨171367959506074225144634389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 228490612674765633526179185 171367959506074225144634389)
                ·
                  refine ⟨8032873101847229303654737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 171367959506074225144634389 8032873101847229303654737)
                  ·
                    refine ⟨6024654826385421977741053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8032873101847229303654737 6024654826385421977741053)
                    ·
                      refine ⟨2259245559894533241652895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6024654826385421977741053 2259245559894533241652895)
                      ·
                        rfl

theorem cell23_4399865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 6, 2, 3].length) (baseStart_4399865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4399865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4399865 prefixEnd_4399865 := by exact prefixLift 4399865
  have htrace : WordTrace (prefixWord ++ tailWord_4399865) baseStart_4399865 baseEnd_4399865 := by
    simpa [prefixWord, tailWord_4399865, baseEnd_4399865] using wordTrace_append hprefix tailTrace_4399865
  have hstable : (prefixWord ++ tailWord_4399865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4399865).length < 2 ^ (prefixWord ++ tailWord_4399865).sum := by decide
  have hdescent : baseEnd_4399865 < baseStart_4399865 := by decide
  rcases family_descends (prefixWord ++ tailWord_4399865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4399882 : List Nat := [3, 1, 2, 2, 1, 2, 3, 2, 2, 2, 3]
def baseStart_4399882 : Nat := 118140960795 + 4399882 * 2 ^ 59
def prefixEnd_4399882 : Nat := 4983230072969 + 3 ^ 40 * 4399882 * 2
def baseEnd_4399882 : Nat := 2259254289065659675140317

theorem tailTrace_4399882 : CollatzResearch.WordTrace tailWord_4399882 prefixEnd_4399882 2259254289065659675140317 := by
  unfold tailWord_4399882
  simp only [CollatzResearch.WordTrace]
  refine ⟨40119220061496607216378475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106984586830657619243675933 40119220061496607216378475)
  ·
    refine ⟨60178830092244910824567713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40119220061496607216378475 60178830092244910824567713)
    ·
      refine ⟨45134122569183683118425785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60178830092244910824567713 45134122569183683118425785)
      ·
        refine ⟨33850591926887762338819339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45134122569183683118425785 33850591926887762338819339)
        ·
          refine ⟨50775887890331643508229009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33850591926887762338819339 50775887890331643508229009)
          ·
            refine ⟨38081915917748732631171757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50775887890331643508229009 38081915917748732631171757)
            ·
              refine ⟨14280718469155774736689409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38081915917748732631171757 14280718469155774736689409)
              ·
                refine ⟨10710538851866831052517057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14280718469155774736689409 10710538851866831052517057)
                ·
                  refine ⟨8032904138900123289387793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10710538851866831052517057 8032904138900123289387793)
                  ·
                    refine ⟨6024678104175092467040845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8032904138900123289387793 6024678104175092467040845)
                    ·
                      refine ⟨2259254289065659675140317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6024678104175092467040845 2259254289065659675140317)
                      ·
                        rfl

theorem cell23_4399882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 2, 2, 2, 3].length) (baseStart_4399882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4399882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4399882 prefixEnd_4399882 := by exact prefixLift 4399882
  have htrace : WordTrace (prefixWord ++ tailWord_4399882) baseStart_4399882 baseEnd_4399882 := by
    simpa [prefixWord, tailWord_4399882, baseEnd_4399882] using wordTrace_append hprefix tailTrace_4399882
  have hstable : (prefixWord ++ tailWord_4399882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4399882).length < 2 ^ (prefixWord ++ tailWord_4399882).sum := by decide
  have hdescent : baseEnd_4399882 < baseStart_4399882 := by decide
  rcases family_descends (prefixWord ++ tailWord_4399882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4399955 : List Nat := [1, 1, 1, 2, 1, 1, 3, 6, 1, 1, 5]
def baseStart_4399955 : Nat := 118140960795 + 4399955 * 2 ^ 59
def prefixEnd_4399955 : Nat := 4983230072969 + 3 ^ 40 * 4399955 * 2
def baseEnd_4399955 : Nat := 2259291773153437889527481

theorem tailTrace_4399955 : CollatzResearch.WordTrace tailWord_4399955 prefixEnd_4399955 2259291773153437889527481 := by
  unfold tailWord_4399955
  simp only [CollatzResearch.WordTrace]
  refine ⟨160479542774721962332921319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106986361849814641555280879 160479542774721962332921319)
  ·
    refine ⟨240719314162082943499381979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160479542774721962332921319 240719314162082943499381979)
    ·
      refine ⟨361078971243124415249072969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240719314162082943499381979 361078971243124415249072969)
      ·
        refine ⟨270809228432343311436804727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 361078971243124415249072969 270809228432343311436804727)
        ·
          refine ⟨406213842648514967155207091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270809228432343311436804727 406213842648514967155207091)
          ·
            refine ⟨609320763972772450732810637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 406213842648514967155207091 609320763972772450732810637)
            ·
              refine ⟨228495286489789669024803989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 609320763972772450732810637 228495286489789669024803989)
              ·
                refine ⟨10710716554208890735537687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 228495286489789669024803989 10710716554208890735537687)
                ·
                  refine ⟨16066074831313336103306531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10710716554208890735537687 16066074831313336103306531)
                  ·
                    refine ⟨24099112246970004154959797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16066074831313336103306531 24099112246970004154959797)
                    ·
                      refine ⟨2259291773153437889527481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24099112246970004154959797 2259291773153437889527481)
                      ·
                        rfl

theorem cell23_4399955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 6, 1, 1, 5].length) (baseStart_4399955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4399955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4399955 prefixEnd_4399955 := by exact prefixLift 4399955
  have htrace : WordTrace (prefixWord ++ tailWord_4399955) baseStart_4399955 baseEnd_4399955 := by
    simpa [prefixWord, tailWord_4399955, baseEnd_4399955] using wordTrace_append hprefix tailTrace_4399955
  have hstable : (prefixWord ++ tailWord_4399955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4399955).length < 2 ^ (prefixWord ++ tailWord_4399955).sum := by decide
  have hdescent : baseEnd_4399955 < baseStart_4399955 := by decide
  rcases family_descends (prefixWord ++ tailWord_4399955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4399962 : List Nat := [3, 1, 1, 2, 1, 5, 2, 1, 1, 6]
def baseStart_4399962 : Nat := 118140960795 + 4399962 * 2 ^ 59
def prefixEnd_4399962 : Nat := 4983230072969 + 3 ^ 40 * 4399962 * 2
def baseEnd_4399962 : Nat := 753098455839339787379983

theorem tailTrace_4399962 : CollatzResearch.WordTrace tailWord_4399962 prefixEnd_4399962 753098455839339787379983 := by
  unfold tailWord_4399962
  simp only [CollatzResearch.WordTrace]
  refine ⟨40119949521424150632106535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106986532057131068352284093 40119949521424150632106535)
  ·
    refine ⟨60179924282136225948159803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40119949521424150632106535 60179924282136225948159803)
    ·
      refine ⟨90269886423204338922239705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60179924282136225948159803 90269886423204338922239705)
      ·
        refine ⟨67702414817403254191679779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90269886423204338922239705 67702414817403254191679779)
        ·
          refine ⟨101553622226104881287519669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67702414817403254191679779 101553622226104881287519669)
          ·
            refine ⟨9520652083697332620704969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 101553622226104881287519669 9520652083697332620704969)
            ·
              refine ⟨7140489062772999465528727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9520652083697332620704969 7140489062772999465528727)
              ·
                refine ⟨10710733594159499198293091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7140489062772999465528727 10710733594159499198293091)
                ·
                  refine ⟨16066100391239248797439637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10710733594159499198293091 16066100391239248797439637)
                  ·
                    refine ⟨753098455839339787379983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16066100391239248797439637 753098455839339787379983)
                    ·
                      rfl

theorem cell23_4399962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 1, 1, 6].length) (baseStart_4399962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4399962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4399962 prefixEnd_4399962 := by exact prefixLift 4399962
  have htrace : WordTrace (prefixWord ++ tailWord_4399962) baseStart_4399962 baseEnd_4399962 := by
    simpa [prefixWord, tailWord_4399962, baseEnd_4399962] using wordTrace_append hprefix tailTrace_4399962
  have hstable : (prefixWord ++ tailWord_4399962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4399962).length < 2 ^ (prefixWord ++ tailWord_4399962).sum := by decide
  have hdescent : baseEnd_4399962 < baseStart_4399962 := by decide
  rcases family_descends (prefixWord ++ tailWord_4399962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4400026 : List Nat := [3, 1, 1, 4, 4, 1, 2, 7]
def baseStart_4400026 : Nat := 118140960795 + 4400026 * 2 ^ 59
def prefixEnd_4400026 : Nat := 4983230072969 + 3 ^ 40 * 4400026 * 2
def baseEnd_4400026 : Nat := 83678823343700263397765

theorem tailTrace_4400026 : CollatzResearch.WordTrace tailWord_4400026 prefixEnd_4400026 83678823343700263397765 := by
  unfold tailWord_4400026
  simp only [CollatzResearch.WordTrace]
  refine ⟨40120533089366185364688983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106988088238309827639170621 40120533089366185364688983)
  ·
    refine ⟨60180799634049278047033475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40120533089366185364688983 60180799634049278047033475)
    ·
      refine ⟨90271199451073917070550213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60180799634049278047033475 90271199451073917070550213)
      ·
        refine ⟨16925849897076359450728165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90271199451073917070550213 16925849897076359450728165)
        ·
          refine ⟨3173596855701817397011531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16925849897076359450728165 3173596855701817397011531)
          ·
            refine ⟨4760395283552726095517297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3173596855701817397011531 4760395283552726095517297)
            ·
              refine ⟨3570296462664544571637973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4760395283552726095517297 3570296462664544571637973)
              ·
                refine ⟨83678823343700263397765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3570296462664544571637973 83678823343700263397765)
                ·
                  rfl

theorem cell23_4400026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 2, 7].length) (baseStart_4400026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4400026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4400026 prefixEnd_4400026 := by exact prefixLift 4400026
  have htrace : WordTrace (prefixWord ++ tailWord_4400026) baseStart_4400026 baseEnd_4400026 := by
    simpa [prefixWord, tailWord_4400026, baseEnd_4400026] using wordTrace_append hprefix tailTrace_4400026
  have hstable : (prefixWord ++ tailWord_4400026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4400026).length < 2 ^ (prefixWord ++ tailWord_4400026).sum := by decide
  have hdescent : baseEnd_4400026 < baseStart_4400026 := by decide
  rcases family_descends (prefixWord ++ tailWord_4400026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4400035 : List Nat := [1, 1, 1, 4, 1, 2, 2, 2, 1, 8]
def baseStart_4400035 : Nat := 118140960795 + 4400035 * 2 ^ 59
def prefixEnd_4400035 : Nat := 4983230072969 + 3 ^ 40 * 4400035 * 2
def baseEnd_4400035 : Nat := 753110950535265858842371

theorem tailTrace_4400035 : CollatzResearch.WordTrace tailWord_4400035 prefixEnd_4400035 753110950535265858842371 := by
  unfold tailWord_4400035
  simp only [CollatzResearch.WordTrace]
  refine ⟨160482460614432135995833559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106988307076288090663889039 160482460614432135995833559)
  ·
    refine ⟨240723690921648203993750339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160482460614432135995833559 240723690921648203993750339)
    ·
      refine ⟨361085536382472305990625509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240723690921648203993750339 361085536382472305990625509)
      ·
        refine ⟨67703538071713557373242283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 361085536382472305990625509 67703538071713557373242283)
        ·
          refine ⟨101555307107570336059863425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67703538071713557373242283 101555307107570336059863425)
          ·
            refine ⟨76166480330677752044897569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101555307107570336059863425 76166480330677752044897569)
            ·
              refine ⟨57124860248008314033673177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76166480330677752044897569 57124860248008314033673177)
              ·
                refine ⟨42843645186006235525254883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57124860248008314033673177 42843645186006235525254883)
                ·
                  refine ⟨64265467779009353287882325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42843645186006235525254883 64265467779009353287882325)
                  ·
                    refine ⟨753110950535265858842371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 64265467779009353287882325 753110950535265858842371)
                    ·
                      rfl

theorem cell23_4400035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 8].length) (baseStart_4400035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4400035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4400035 prefixEnd_4400035 := by exact prefixLift 4400035
  have htrace : WordTrace (prefixWord ++ tailWord_4400035) baseStart_4400035 baseEnd_4400035 := by
    simpa [prefixWord, tailWord_4400035, baseEnd_4400035] using wordTrace_append hprefix tailTrace_4400035
  have hstable : (prefixWord ++ tailWord_4400035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4400035).length < 2 ^ (prefixWord ++ tailWord_4400035).sum := by decide
  have hdescent : baseEnd_4400035 < baseStart_4400035 := by decide
  rcases family_descends (prefixWord ++ tailWord_4400035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4400054 : List Nat := [5, 1, 4, 1, 1, 2, 1, 1, 3, 2, 2]
def baseStart_4400054 : Nat := 118140960795 + 4400054 * 2 ^ 59
def prefixEnd_4400054 : Nat := 4983230072969 + 3 ^ 40 * 4400054 * 2
def baseEnd_4400054 : Nat := 2259342607738233002189527

theorem tailTrace_4400054 : CollatzResearch.WordTrace tailWord_4400054 prefixEnd_4400054 2259342607738233002189527 := by
  unfold tailWord_4400054
  simp only [CollatzResearch.WordTrace]
  refine ⟨10030197100085206390048451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 106988769067575534827183477 10030197100085206390048451)
  ·
    refine ⟨15045295650127809585072677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10030197100085206390048451 15045295650127809585072677)
    ·
      refine ⟨2820992934398964297201127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15045295650127809585072677 2820992934398964297201127)
      ·
        refine ⟨4231489401598446445801691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2820992934398964297201127 4231489401598446445801691)
        ·
          refine ⟨6347234102397669668702537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4231489401598446445801691 6347234102397669668702537)
          ·
            refine ⟨4760425576798252251526903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6347234102397669668702537 4760425576798252251526903)
            ·
              refine ⟨7140638365197378377290355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4760425576798252251526903 7140638365197378377290355)
              ·
                refine ⟨10710957547796067565935533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7140638365197378377290355 10710957547796067565935533)
                ·
                  refine ⟨4016609080423525337225825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10710957547796067565935533 4016609080423525337225825)
                  ·
                    refine ⟨3012456810317644002919369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4016609080423525337225825 3012456810317644002919369)
                    ·
                      refine ⟨2259342607738233002189527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3012456810317644002919369 2259342607738233002189527)
                      ·
                        rfl

theorem cell23_4400054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_4400054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4400054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4400054 prefixEnd_4400054 := by exact prefixLift 4400054
  have htrace : WordTrace (prefixWord ++ tailWord_4400054) baseStart_4400054 baseEnd_4400054 := by
    simpa [prefixWord, tailWord_4400054, baseEnd_4400054] using wordTrace_append hprefix tailTrace_4400054
  have hstable : (prefixWord ++ tailWord_4400054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4400054).length < 2 ^ (prefixWord ++ tailWord_4400054).sum := by decide
  have hdescent : baseEnd_4400054 < baseStart_4400054 := by decide
  rcases family_descends (prefixWord ++ tailWord_4400054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4400059 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 8, 2, 2]
def baseStart_4400059 : Nat := 118140960795 + 4400059 * 2 ^ 59
def prefixEnd_4400059 : Nat := 4983230072969 + 3 ^ 40 * 4400059 * 2
def baseEnd_4400059 : Nat := 2259345175141505482627003

theorem tailTrace_4400059 : CollatzResearch.WordTrace tailWord_4400059 prefixEnd_4400059 2259345175141505482627003 := by
  unfold tailWord_4400059
  simp only [CollatzResearch.WordTrace]
  refine ⟨160483335966345188094707231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106988890644230125396471487 160483335966345188094707231)
  ·
    refine ⟨240725003949517782142060847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160483335966345188094707231 240725003949517782142060847)
    ·
      refine ⟨361087505924276673213091271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240725003949517782142060847 361087505924276673213091271)
      ·
        refine ⟨541631258886415009819636907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 361087505924276673213091271 541631258886415009819636907)
        ·
          refine ⟨812446888329622514729455361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 541631258886415009819636907 812446888329622514729455361)
          ·
            refine ⟨609335166247216886047091521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 812446888329622514729455361 609335166247216886047091521)
            ·
              refine ⟨457001374685412664535318641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 609335166247216886047091521 457001374685412664535318641)
              ·
                refine ⟨342751031014059498401488981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 457001374685412664535318641 342751031014059498401488981)
                ·
                  refine ⟨4016613644696009746892449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 342751031014059498401488981 4016613644696009746892449)
                  ·
                    refine ⟨3012460233522007310169337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4016613644696009746892449 3012460233522007310169337)
                    ·
                      refine ⟨2259345175141505482627003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3012460233522007310169337 2259345175141505482627003)
                      ·
                        rfl

theorem cell23_4400059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 8, 2, 2].length) (baseStart_4400059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4400059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4400059 prefixEnd_4400059 := by exact prefixLift 4400059
  have htrace : WordTrace (prefixWord ++ tailWord_4400059) baseStart_4400059 baseEnd_4400059 := by
    simpa [prefixWord, tailWord_4400059, baseEnd_4400059] using wordTrace_append hprefix tailTrace_4400059
  have hstable : (prefixWord ++ tailWord_4400059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4400059).length < 2 ^ (prefixWord ++ tailWord_4400059).sum := by decide
  have hdescent : baseEnd_4400059 < baseStart_4400059 := by decide
  rcases family_descends (prefixWord ++ tailWord_4400059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4400062 : List Nat := [4, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5]
def baseStart_4400062 : Nat := 118140960795 + 4400062 * 2 ^ 59
def prefixEnd_4400062 : Nat := 4983230072969 + 3 ^ 40 * 4400062 * 2
def baseEnd_4400062 : Nat := 2259346715583468970889489

theorem tailTrace_4400062 : CollatzResearch.WordTrace tailWord_4400062 prefixEnd_4400062 2259346715583468970889489 := by
  unfold tailWord_4400062
  simp only [CollatzResearch.WordTrace]
  refine ⟨20060430673166789950883305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106988963590222879738044293 20060430673166789950883305)
  ·
    refine ⟨15045323004875092463162479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20060430673166789950883305 15045323004875092463162479)
    ·
      refine ⟨22567984507312638694743719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15045323004875092463162479 22567984507312638694743719)
      ·
        refine ⟨33851976760968958042115579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22567984507312638694743719 33851976760968958042115579)
        ·
          refine ⟨50777965141453437063173369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33851976760968958042115579 50777965141453437063173369)
          ·
            refine ⟨38083473856090077797380027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50777965141453437063173369 38083473856090077797380027)
            ·
              refine ⟨57125210784135116696070041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38083473856090077797380027 57125210784135116696070041)
              ·
                refine ⟨42843908088101337522052531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57125210784135116696070041 42843908088101337522052531)
                ·
                  refine ⟨64265862132152006283078797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42843908088101337522052531 64265862132152006283078797)
                  ·
                    refine ⟨24099698299557002356154549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 64265862132152006283078797 24099698299557002356154549)
                    ·
                      refine ⟨2259346715583468970889489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24099698299557002356154549 2259346715583468970889489)
                      ·
                        rfl

theorem cell23_4400062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_4400062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4400062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4400062 prefixEnd_4400062 := by exact prefixLift 4400062
  have htrace : WordTrace (prefixWord ++ tailWord_4400062) baseStart_4400062 baseEnd_4400062 := by
    simpa [prefixWord, tailWord_4400062, baseEnd_4400062] using wordTrace_append hprefix tailTrace_4400062
  have hstable : (prefixWord ++ tailWord_4400062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4400062).length < 2 ^ (prefixWord ++ tailWord_4400062).sum := by decide
  have hdescent : baseEnd_4400062 < baseStart_4400062 := by decide
  rcases family_descends (prefixWord ++ tailWord_4400062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4400099 : List Nat := [1, 1, 1, 6, 1, 1, 2, 5, 5]
def baseStart_4400099 : Nat := 118140960795 + 4400099 * 2 ^ 59
def prefixEnd_4400099 : Nat := 4983230072969 + 3 ^ 40 * 4400099 * 2
def baseEnd_4400099 : Nat := 251040634929742814014091

theorem tailTrace_4400099 : CollatzResearch.WordTrace tailWord_4400099 prefixEnd_4400099 251040634929742814014091 := by
  unfold tailWord_4400099
  simp only [CollatzResearch.WordTrace]
  refine ⟨160484794886200274926163351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106989863257466849950775567 160484794886200274926163351)
  ·
    refine ⟨240727192329300412389245027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160484794886200274926163351 240727192329300412389245027)
    ·
      refine ⟨361090788493950618583867541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240727192329300412389245027 361090788493950618583867541)
      ·
        refine ⟨16926130710653935246118791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 361090788493950618583867541 16926130710653935246118791)
        ·
          refine ⟨25389196065980902869178187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16926130710653935246118791 25389196065980902869178187)
          ·
            refine ⟨38083794098971354303767281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25389196065980902869178187 38083794098971354303767281)
            ·
              refine ⟨28562845574228515727825461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38083794098971354303767281 28562845574228515727825461)
              ·
                refine ⟨2677766772583923349483637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28562845574228515727825461 2677766772583923349483637)
                ·
                  refine ⟨251040634929742814014091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2677766772583923349483637 251040634929742814014091)
                  ·
                    rfl

theorem cell23_4400099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 5, 5].length) (baseStart_4400099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4400099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4400099 prefixEnd_4400099 := by exact prefixLift 4400099
  have htrace : WordTrace (prefixWord ++ tailWord_4400099) baseStart_4400099 baseEnd_4400099 := by
    simpa [prefixWord, tailWord_4400099, baseEnd_4400099] using wordTrace_append hprefix tailTrace_4400099
  have hstable : (prefixWord ++ tailWord_4400099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4400099).length < 2 ^ (prefixWord ++ tailWord_4400099).sum := by decide
  have hdescent : baseEnd_4400099 < baseStart_4400099 := by decide
  rcases family_descends (prefixWord ++ tailWord_4400099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4400110 : List Nat := [4, 1, 2, 1, 4, 1, 2, 2, 2, 2, 2]
def baseStart_4400110 : Nat := 118140960795 + 4400110 * 2 ^ 59
def prefixEnd_4400110 : Nat := 4983230072969 + 3 ^ 40 * 4400110 * 2
def baseEnd_4400110 : Nat := 2259371362654884783089269

theorem tailTrace_4400110 : CollatzResearch.WordTrace tailWord_4400110 prefixEnd_4400110 2259371362654884783089269 := by
  unfold tailWord_4400110
  simp only [CollatzResearch.WordTrace]
  refine ⟨20060649511145052975601723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106990130726106949203209189 20060649511145052975601723)
  ·
    refine ⟨30090974266717579463402585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20060649511145052975601723 30090974266717579463402585)
    ·
      refine ⟨22568230700038184597551939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30090974266717579463402585 22568230700038184597551939)
      ·
        refine ⟨33852346050057276896327909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22568230700038184597551939 33852346050057276896327909)
        ·
          refine ⟨6347314884385739418061483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33852346050057276896327909 6347314884385739418061483)
          ·
            refine ⟨9520972326578609127092225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6347314884385739418061483 9520972326578609127092225)
            ·
              refine ⟨7140729244933956845319169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9520972326578609127092225 7140729244933956845319169)
              ·
                refine ⟨5355546933700467633989377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7140729244933956845319169 5355546933700467633989377)
                ·
                  refine ⟨4016660200275350725492033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5355546933700467633989377 4016660200275350725492033)
                  ·
                    refine ⟨3012495150206513044119025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4016660200275350725492033 3012495150206513044119025)
                    ·
                      refine ⟨2259371362654884783089269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3012495150206513044119025 2259371362654884783089269)
                      ·
                        rfl

theorem cell23_4400110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 2, 2, 2, 2].length) (baseStart_4400110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4400110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4400110 prefixEnd_4400110 := by exact prefixLift 4400110
  have htrace : WordTrace (prefixWord ++ tailWord_4400110) baseStart_4400110 baseEnd_4400110 := by
    simpa [prefixWord, tailWord_4400110, baseEnd_4400110] using wordTrace_append hprefix tailTrace_4400110
  have hstable : (prefixWord ++ tailWord_4400110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4400110).length < 2 ^ (prefixWord ++ tailWord_4400110).sum := by decide
  have hdescent : baseEnd_4400110 < baseStart_4400110 := by decide
  rcases family_descends (prefixWord ++ tailWord_4400110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4400149 : List Nat := [1, 3, 2, 1, 4, 2, 1, 1, 1, 3, 4]
def baseStart_4400149 : Nat := 118140960795 + 4400149 * 2 ^ 59
def prefixEnd_4400149 : Nat := 4983230072969 + 3 ^ 40 * 4400149 * 2
def baseEnd_4400149 : Nat := 2259391388400410130501589

theorem tailTrace_4400149 : CollatzResearch.WordTrace tailWord_4400149 prefixEnd_4400149 2259391388400410130501589 := by
  unfold tailWord_4400149
  simp only [CollatzResearch.WordTrace]
  refine ⟨160486618536019133465483501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106991079024012755643655667 160486618536019133465483501)
  ·
    refine ⟨60182481951007175049556313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160486618536019133465483501 60182481951007175049556313)
    ·
      refine ⟨45136861463255381287167235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60182481951007175049556313 45136861463255381287167235)
      ·
        refine ⟨67705292194883071930750853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45136861463255381287167235 67705292194883071930750853)
        ·
          refine ⟨12694742286540575987015785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67705292194883071930750853 12694742286540575987015785)
          ·
            refine ⟨9521056714905431990261839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12694742286540575987015785 9521056714905431990261839)
            ·
              refine ⟨14281585072358147985392759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9521056714905431990261839 14281585072358147985392759)
              ·
                refine ⟨21422377608537221978089139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14281585072358147985392759 21422377608537221978089139)
                ·
                  refine ⟨32133566412805832967133709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21422377608537221978089139 32133566412805832967133709)
                  ·
                    refine ⟨12050087404802187362675141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32133566412805832967133709 12050087404802187362675141)
                    ·
                      refine ⟨2259391388400410130501589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12050087404802187362675141 2259391388400410130501589)
                      ·
                        rfl

theorem cell23_4400149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 3, 4].length) (baseStart_4400149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4400149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4400149 prefixEnd_4400149 := by exact prefixLift 4400149
  have htrace : WordTrace (prefixWord ++ tailWord_4400149) baseStart_4400149 baseEnd_4400149 := by
    simpa [prefixWord, tailWord_4400149, baseEnd_4400149] using wordTrace_append hprefix tailTrace_4400149
  have hstable : (prefixWord ++ tailWord_4400149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4400149).length < 2 ^ (prefixWord ++ tailWord_4400149).sum := by decide
  have hdescent : baseEnd_4400149 < baseStart_4400149 := by decide
  rcases family_descends (prefixWord ++ tailWord_4400149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4400172 : List Nat := [2, 2, 1, 1, 1, 2, 5, 1, 8]
def baseStart_4400172 : Nat := 118140960795 + 4400172 * 2 ^ 59
def prefixEnd_4400172 : Nat := 4983230072969 + 3 ^ 40 * 4400172 * 2
def baseEnd_4400172 : Nat := 251044799828384837834887

theorem tailTrace_4400172 : CollatzResearch.WordTrace tailWord_4400172 prefixEnd_4400172 251044799828384837834887 := by
  unfold tailWord_4400172
  simp only [CollatzResearch.WordTrace]
  refine ⟨80243728707467904196785385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106991638276623872262380513 80243728707467904196785385)
  ·
    refine ⟨60182796530600928147589039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80243728707467904196785385 60182796530600928147589039)
    ·
      refine ⟨90274194795901392221383559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60182796530600928147589039 90274194795901392221383559)
      ·
        refine ⟨135411292193852088332075339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90274194795901392221383559 135411292193852088332075339)
        ·
          refine ⟨203116938290778132498113009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135411292193852088332075339 203116938290778132498113009)
          ·
            refine ⟨152337703718083599373584757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 203116938290778132498113009 152337703718083599373584757)
            ·
              refine ⟨14281659723570337441273571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 152337703718083599373584757 14281659723570337441273571)
              ·
                refine ⟨21422489585355506161910357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14281659723570337441273571 21422489585355506161910357)
                ·
                  refine ⟨251044799828384837834887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21422489585355506161910357 251044799828384837834887)
                  ·
                    rfl

theorem cell23_4400172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 8].length) (baseStart_4400172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4400172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4400172 prefixEnd_4400172 := by exact prefixLift 4400172
  have htrace : WordTrace (prefixWord ++ tailWord_4400172) baseStart_4400172 baseEnd_4400172 := by
    simpa [prefixWord, tailWord_4400172, baseEnd_4400172] using wordTrace_append hprefix tailTrace_4400172
  have hstable : (prefixWord ++ tailWord_4400172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4400172).length < 2 ^ (prefixWord ++ tailWord_4400172).sum := by decide
  have hdescent : baseEnd_4400172 < baseStart_4400172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4400172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4400176 : List Nat := [2, 1, 1, 1, 2, 4, 1, 6, 1, 4]
def baseStart_4400176 : Nat := 118140960795 + 4400176 * 2 ^ 59
def prefixEnd_4400176 : Nat := 4983230072969 + 3 ^ 40 * 4400176 * 2
def baseEnd_4400176 : Nat := 753135084126027174954655

theorem tailTrace_4400176 : CollatzResearch.WordTrace tailWord_4400176 prefixEnd_4400176 753135084126027174954655 := by
  unfold tailWord_4400176
  simp only [CollatzResearch.WordTrace]
  refine ⟨80243801653460658538358191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106991735537947544717810921 80243801653460658538358191)
  ·
    refine ⟨120365702480190987807537287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80243801653460658538358191 120365702480190987807537287)
    ·
      refine ⟨180548553720286481711305931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120365702480190987807537287 180548553720286481711305931)
      ·
        refine ⟨270822830580429722566958897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180548553720286481711305931 270822830580429722566958897)
        ·
          refine ⟨203117122935322291925219173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 270822830580429722566958897 203117122935322291925219173)
          ·
            refine ⟨38084460550372929735978595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 203117122935322291925219173 38084460550372929735978595)
            ·
              refine ⟨57126690825559394603967893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38084460550372929735978595 57126690825559394603967893)
              ·
                refine ⟨2677813632448096622060995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 57126690825559394603967893 2677813632448096622060995)
                ·
                  refine ⟨4016720448672144933091493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2677813632448096622060995 4016720448672144933091493)
                  ·
                    refine ⟨753135084126027174954655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4016720448672144933091493 753135084126027174954655)
                    ·
                      rfl

theorem cell23_4400176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 6, 1, 4].length) (baseStart_4400176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4400176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4400176 prefixEnd_4400176 := by exact prefixLift 4400176
  have htrace : WordTrace (prefixWord ++ tailWord_4400176) baseStart_4400176 baseEnd_4400176 := by
    simpa [prefixWord, tailWord_4400176, baseEnd_4400176] using wordTrace_append hprefix tailTrace_4400176
  have hstable : (prefixWord ++ tailWord_4400176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4400176).length < 2 ^ (prefixWord ++ tailWord_4400176).sum := by decide
  have hdescent : baseEnd_4400176 < baseStart_4400176 := by decide
  rcases family_descends (prefixWord ++ tailWord_4400176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4400192 : List Nat := [2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 6]
def baseStart_4400192 : Nat := 118140960795 + 4400192 * 2 ^ 59
def prefixEnd_4400192 : Nat := 4983230072969 + 3 ^ 40 * 4400192 * 2
def baseEnd_4400192 : Nat := 2259413468068553462263891

theorem tailTrace_4400192 : CollatzResearch.WordTrace tailWord_4400192 prefixEnd_4400192 2259413468068553462263891 := by
  unfold tailWord_4400192
  simp only [CollatzResearch.WordTrace]
  refine ⟨80244093437431675904649415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106992124583242234539532553 80244093437431675904649415)
  ·
    refine ⟨120366140156147513856974123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80244093437431675904649415 120366140156147513856974123)
    ·
      refine ⟨180549210234221270785461185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120366140156147513856974123 180549210234221270785461185)
      ·
        refine ⟨135411907675665953089095889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180549210234221270785461185 135411907675665953089095889)
        ·
          refine ⟨101558930756749464816821917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135411907675665953089095889 101558930756749464816821917)
          ·
            refine ⟨38084599033781049306308219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101558930756749464816821917 38084599033781049306308219)
            ·
              refine ⟨57126898550671573959462329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38084599033781049306308219 57126898550671573959462329)
              ·
                refine ⟨42845173913003680469596747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57126898550671573959462329 42845173913003680469596747)
                ·
                  refine ⟨64267760869505520704395121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42845173913003680469596747 64267760869505520704395121)
                  ·
                    refine ⟨48200820652129140528296341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 64267760869505520704395121 48200820652129140528296341)
                    ·
                      refine ⟨2259413468068553462263891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48200820652129140528296341 2259413468068553462263891)
                      ·
                        rfl

theorem cell23_4400192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 6].length) (baseStart_4400192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4400192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4400192 prefixEnd_4400192 := by exact prefixLift 4400192
  have htrace : WordTrace (prefixWord ++ tailWord_4400192) baseStart_4400192 baseEnd_4400192 := by
    simpa [prefixWord, tailWord_4400192, baseEnd_4400192] using wordTrace_append hprefix tailTrace_4400192
  have hstable : (prefixWord ++ tailWord_4400192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4400192).length < 2 ^ (prefixWord ++ tailWord_4400192).sum := by decide
  have hdescent : baseEnd_4400192 < baseStart_4400192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4400192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4400210 : List Nat := [3, 2, 2, 1, 3, 3, 1, 3, 1, 4]
def baseStart_4400210 : Nat := 118140960795 + 4400210 * 2 ^ 59
def prefixEnd_4400210 : Nat := 4983230072969 + 3 ^ 40 * 4400210 * 2
def baseEnd_4400210 : Nat := 753140903573444797279603

theorem tailTrace_4400210 : CollatzResearch.WordTrace tailWord_4400210 prefixEnd_4400210 753140903573444797279603 := by
  unfold tailWord_4400210
  simp only [CollatzResearch.WordTrace]
  refine ⟨40122210847199535220863521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106992562259198760588969389 40122210847199535220863521)
  ·
    refine ⟨30091658135399651415647641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40122210847199535220863521 30091658135399651415647641)
    ·
      refine ⟨22568743601549738561735731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30091658135399651415647641 22568743601549738561735731)
      ·
        refine ⟨33853115402324607842603597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22568743601549738561735731 33853115402324607842603597)
        ·
          refine ⟨12694918275871727940976349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33853115402324607842603597 12694918275871727940976349)
          ·
            refine ⟨4760594353451897977866131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12694918275871727940976349 4760594353451897977866131)
            ·
              refine ⟨7140891530177846966799197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4760594353451897977866131 7140891530177846966799197)
              ·
                refine ⟨2677834323816692612549699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7140891530177846966799197 2677834323816692612549699)
                ·
                  refine ⟨4016751485725038918824549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2677834323816692612549699 4016751485725038918824549)
                  ·
                    refine ⟨753140903573444797279603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4016751485725038918824549 753140903573444797279603)
                    ·
                      rfl

theorem cell23_4400210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 3, 1, 4].length) (baseStart_4400210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4400210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4400210 prefixEnd_4400210 := by exact prefixLift 4400210
  have htrace : WordTrace (prefixWord ++ tailWord_4400210) baseStart_4400210 baseEnd_4400210 := by
    simpa [prefixWord, tailWord_4400210, baseEnd_4400210] using wordTrace_append hprefix tailTrace_4400210
  have hstable : (prefixWord ++ tailWord_4400210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4400210).length < 2 ^ (prefixWord ++ tailWord_4400210).sum := by decide
  have hdescent : baseEnd_4400210 < baseStart_4400210 := by decide
  rcases family_descends (prefixWord ++ tailWord_4400210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4400233 : List Nat := [1, 2, 1, 1, 1, 8, 1, 1, 3, 1, 3]
def baseStart_4400233 : Nat := 118140960795 + 4400233 * 2 ^ 59
def prefixEnd_4400233 : Nat := 4983230072969 + 3 ^ 40 * 4400233 * 2
def baseEnd_4400233 : Nat := 2259434520775387801851203

theorem tailTrace_4400233 : CollatzResearch.WordTrace tailWord_4400233 prefixEnd_4400233 2259434520775387801851203 := by
  unfold tailWord_4400233
  simp only [CollatzResearch.WordTrace]
  refine ⟨160489682267714815811541353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106993121511809877207694235 160489682267714815811541353)
  ·
    refine ⟨120367261700786111858656015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160489682267714815811541353 120367261700786111858656015)
    ·
      refine ⟨180550892551179167787984023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120367261700786111858656015 180550892551179167787984023)
      ·
        refine ⟨270826338826768751681976035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180550892551179167787984023 270826338826768751681976035)
        ·
          refine ⟨406239508240153127522964053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270826338826768751681976035 406239508240153127522964053)
          ·
            refine ⟨4760619237189294463159735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 406239508240153127522964053 4760619237189294463159735)
            ·
              refine ⟨7140928855783941694739603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4760619237189294463159735 7140928855783941694739603)
              ·
                refine ⟨10711393283675912542109405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7140928855783941694739603 10711393283675912542109405)
                ·
                  refine ⟨4016772481378467203291027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10711393283675912542109405 4016772481378467203291027)
                  ·
                    refine ⟨6025158722067700804936541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4016772481378467203291027 6025158722067700804936541)
                    ·
                      refine ⟨2259434520775387801851203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6025158722067700804936541 2259434520775387801851203)
                      ·
                        rfl

theorem cell23_4400233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 1, 3, 1, 3].length) (baseStart_4400233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4400233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4400233 prefixEnd_4400233 := by exact prefixLift 4400233
  have htrace : WordTrace (prefixWord ++ tailWord_4400233) baseStart_4400233 baseEnd_4400233 := by
    simpa [prefixWord, tailWord_4400233, baseEnd_4400233] using wordTrace_append hprefix tailTrace_4400233
  have hstable : (prefixWord ++ tailWord_4400233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4400233).length < 2 ^ (prefixWord ++ tailWord_4400233).sum := by decide
  have hdescent : baseEnd_4400233 < baseStart_4400233 := by decide
  rcases family_descends (prefixWord ++ tailWord_4400233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4400239 : List Nat := [1, 1, 2, 1, 3, 3, 2, 2, 3, 1, 4]
def baseStart_4400239 : Nat := 118140960795 + 4400239 * 2 ^ 59
def prefixEnd_4400239 : Nat := 4983230072969 + 3 ^ 40 * 4400239 * 2
def baseEnd_4400239 : Nat := 2259437601659314778376175

theorem tailTrace_4400239 : CollatzResearch.WordTrace tailWord_4400239 prefixEnd_4400239 2259437601659314778376175 := by
  unfold tailWord_4400239
  simp only [CollatzResearch.WordTrace]
  refine ⟨160489901105693078836259771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106993267403795385890839847 160489901105693078836259771)
  ·
    refine ⟨240734851658539618254389657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160489901105693078836259771 240734851658539618254389657)
    ·
      refine ⟨180551138743904713690792243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 240734851658539618254389657 180551138743904713690792243)
      ·
        refine ⟨270826708115857070536188365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180551138743904713690792243 270826708115857070536188365)
        ·
          refine ⟨101560015543446401451070637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 270826708115857070536188365 101560015543446401451070637)
          ·
            refine ⟨38085005828792400544151489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101560015543446401451070637 38085005828792400544151489)
            ·
              refine ⟨28563754371594300408113617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38085005828792400544151489 28563754371594300408113617)
              ·
                refine ⟨21422815778695725306085213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28563754371594300408113617 21422815778695725306085213)
                ·
                  refine ⟨8033555917010896989781955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21422815778695725306085213 8033555917010896989781955)
                  ·
                    refine ⟨12050333875516345484672933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8033555917010896989781955 12050333875516345484672933)
                    ·
                      refine ⟨2259437601659314778376175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12050333875516345484672933 2259437601659314778376175)
                      ·
                        rfl

theorem cell23_4400239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 3, 1, 4].length) (baseStart_4400239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4400239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4400239 prefixEnd_4400239 := by exact prefixLift 4400239
  have htrace : WordTrace (prefixWord ++ tailWord_4400239) baseStart_4400239 baseEnd_4400239 := by
    simpa [prefixWord, tailWord_4400239, baseEnd_4400239] using wordTrace_append hprefix tailTrace_4400239
  have hstable : (prefixWord ++ tailWord_4400239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4400239).length < 2 ^ (prefixWord ++ tailWord_4400239).sum := by decide
  have hdescent : baseEnd_4400239 < baseStart_4400239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4400239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4400256 : List Nat := [2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 4]
def baseStart_4400256 : Nat := 118140960795 + 4400256 * 2 ^ 59
def prefixEnd_4400256 : Nat := 4983230072969 + 3 ^ 40 * 4400256 * 2
def baseEnd_4400256 : Nat := 2259446330830441211863597

theorem tailTrace_4400256 : CollatzResearch.WordTrace tailWord_4400256 prefixEnd_4400256 2259446330830441211863597 := by
  unfold tailWord_4400256
  simp only [CollatzResearch.WordTrace]
  refine ⟨80245260573315745369814311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106993680764420993826419081 80245260573315745369814311)
  ·
    refine ⟨120367890859973618054721467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80245260573315745369814311 120367890859973618054721467)
    ·
      refine ⟨180551836289960427082082201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120367890859973618054721467 180551836289960427082082201)
      ·
        refine ⟨135413877217470320311561651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180551836289960427082082201 135413877217470320311561651)
        ·
          refine ⟨203120815826205480467342477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135413877217470320311561651 203120815826205480467342477)
          ·
            refine ⟨76170305934827055175253429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 203120815826205480467342477 76170305934827055175253429)
            ·
              refine ⟨7140966181390036422680009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 76170305934827055175253429 7140966181390036422680009)
              ·
                refine ⟨5355724636042527317010007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7140966181390036422680009 5355724636042527317010007)
                ·
                  refine ⟨8033586954063790975515011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5355724636042527317010007 8033586954063790975515011)
                  ·
                    refine ⟨12050380431095686463272517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8033586954063790975515011 12050380431095686463272517)
                    ·
                      refine ⟨2259446330830441211863597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12050380431095686463272517 2259446330830441211863597)
                      ·
                        rfl

theorem cell23_4400256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 4].length) (baseStart_4400256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4400256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4400256 prefixEnd_4400256 := by exact prefixLift 4400256
  have htrace : WordTrace (prefixWord ++ tailWord_4400256) baseStart_4400256 baseEnd_4400256 := by
    simpa [prefixWord, tailWord_4400256, baseEnd_4400256] using wordTrace_append hprefix tailTrace_4400256
  have hstable : (prefixWord ++ tailWord_4400256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4400256).length < 2 ^ (prefixWord ++ tailWord_4400256).sum := by decide
  have hdescent : baseEnd_4400256 < baseStart_4400256 := by decide
  rcases family_descends (prefixWord ++ tailWord_4400256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4400306 : List Nat := [3, 2, 1, 1, 1, 4, 1, 3, 1, 3, 3]
def baseStart_4400306 : Nat := 118140960795 + 4400306 * 2 ^ 59
def prefixEnd_4400306 : Nat := 4983230072969 + 3 ^ 40 * 4400306 * 2
def baseEnd_4400306 : Nat := 2259472004863166016238367

theorem tailTrace_4400306 : CollatzResearch.WordTrace tailWord_4400306 prefixEnd_4400306 2259472004863166016238367 := by
  unfold tailWord_4400306
  simp only [CollatzResearch.WordTrace]
  refine ⟨40123086199112587319737193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106994896530966899519299181 40123086199112587319737193)
  ·
    refine ⟨30092314649334440489802895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40123086199112587319737193 30092314649334440489802895)
    ·
      refine ⟨45138471974001660734704343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30092314649334440489802895 45138471974001660734704343)
      ·
        refine ⟨67707707961002491102056515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45138471974001660734704343 67707707961002491102056515)
        ·
          refine ⟨101561561941503736653084773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67707707961002491102056515 101561561941503736653084773)
          ·
            refine ⟨19042792864031950622453395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 101561561941503736653084773 19042792864031950622453395)
            ·
              refine ⟨28564189296047925933680093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19042792864031950622453395 28564189296047925933680093)
              ·
                refine ⟨10711570986017972225130035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28564189296047925933680093 10711570986017972225130035)
                ·
                  refine ⟨16067356479026958337695053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10711570986017972225130035 16067356479026958337695053)
                  ·
                    refine ⟨6025258679635109376635645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16067356479026958337695053 6025258679635109376635645)
                    ·
                      refine ⟨2259472004863166016238367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6025258679635109376635645 2259472004863166016238367)
                      ·
                        rfl

theorem cell23_4400306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 3, 1, 3, 3].length) (baseStart_4400306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4400306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4400306 prefixEnd_4400306 := by exact prefixLift 4400306
  have htrace : WordTrace (prefixWord ++ tailWord_4400306) baseStart_4400306 baseEnd_4400306 := by
    simpa [prefixWord, tailWord_4400306, baseEnd_4400306] using wordTrace_append hprefix tailTrace_4400306
  have hstable : (prefixWord ++ tailWord_4400306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4400306).length < 2 ^ (prefixWord ++ tailWord_4400306).sum := by decide
  have hdescent : baseEnd_4400306 < baseStart_4400306 := by decide
  rcases family_descends (prefixWord ++ tailWord_4400306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4400324 : List Nat := [2, 3, 3, 1, 3, 1, 2, 3, 1, 2, 2]
def baseStart_4400324 : Nat := 118140960795 + 4400324 * 2 ^ 59
def prefixEnd_4400324 : Nat := 4983230072969 + 3 ^ 40 * 4400324 * 2
def baseEnd_4400324 : Nat := 2259481247514946945813285

theorem tailTrace_4400324 : CollatzResearch.WordTrace tailWord_4400324 prefixEnd_4400324 2259481247514946945813285 := by
  unfold tailWord_4400324
  simp only [CollatzResearch.WordTrace]
  refine ⟨80246500655192569176552013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106995334206923425568736017 80246500655192569176552013)
  ·
    refine ⟨30092437745697213441207005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80246500655192569176552013 30092437745697213441207005)
    ·
      refine ⟨11284664154636455040452627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30092437745697213441207005 11284664154636455040452627)
      ·
        refine ⟨16926996231954682560678941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11284664154636455040452627 16926996231954682560678941)
        ·
          refine ⟨6347623586983005960254603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16926996231954682560678941 6347623586983005960254603)
          ·
            refine ⟨9521435380474508940381905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6347623586983005960254603 9521435380474508940381905)
            ·
              refine ⟨7141076535355881705286429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9521435380474508940381905 7141076535355881705286429)
              ·
                refine ⟨2677903700758455639482411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7141076535355881705286429 2677903700758455639482411)
                ·
                  refine ⟨4016855551137683459223617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2677903700758455639482411 4016855551137683459223617)
                  ·
                    refine ⟨3012641663353262594417713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4016855551137683459223617 3012641663353262594417713)
                    ·
                      refine ⟨2259481247514946945813285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3012641663353262594417713 2259481247514946945813285)
                      ·
                        rfl

theorem cell23_4400324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 3, 1, 2, 2].length) (baseStart_4400324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4400324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4400324 prefixEnd_4400324 := by exact prefixLift 4400324
  have htrace : WordTrace (prefixWord ++ tailWord_4400324) baseStart_4400324 baseEnd_4400324 := by
    simpa [prefixWord, tailWord_4400324, baseEnd_4400324] using wordTrace_append hprefix tailTrace_4400324
  have hstable : (prefixWord ++ tailWord_4400324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4400324).length < 2 ^ (prefixWord ++ tailWord_4400324).sum := by decide
  have hdescent : baseEnd_4400324 < baseStart_4400324 := by decide
  rcases family_descends (prefixWord ++ tailWord_4400324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4400357 : List Nat := [1, 3, 1, 4, 3, 1, 3, 1, 2, 1, 3]
def baseStart_4400357 : Nat := 118140960795 + 4400357 * 2 ^ 59
def prefixEnd_4400357 : Nat := 4983230072969 + 3 ^ 40 * 4400357 * 2
def baseEnd_4400357 : Nat := 2259498192376545316700633

theorem tailTrace_4400357 : CollatzResearch.WordTrace tailWord_4400357 prefixEnd_4400357 2259498192376545316700633 := by
  unfold tailWord_4400357
  simp only [CollatzResearch.WordTrace]
  refine ⟨160494204919265584989055325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106996136612843723326036883 160494204919265584989055325)
  ·
    refine ⟨60185326844724594370895747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160494204919265584989055325 60185326844724594370895747)
    ·
      refine ⟨90277990267086891556343621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60185326844724594370895747 90277990267086891556343621)
      ·
        refine ⟨16927123175078792166814429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90277990267086891556343621 16927123175078792166814429)
        ·
          refine ⟨6347671190654547062555411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16927123175078792166814429 6347671190654547062555411)
          ·
            refine ⟨9521506785981820593833117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6347671190654547062555411 9521506785981820593833117)
            ·
              refine ⟨3570565044743182722687419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9521506785981820593833117 3570565044743182722687419)
              ·
                refine ⟨5355847567114774084031129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3570565044743182722687419 5355847567114774084031129)
                ·
                  refine ⟨4016885675336080563023347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5355847567114774084031129 4016885675336080563023347)
                  ·
                    refine ⟨6025328513004120844535021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4016885675336080563023347 6025328513004120844535021)
                    ·
                      refine ⟨2259498192376545316700633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6025328513004120844535021 2259498192376545316700633)
                      ·
                        rfl

theorem cell23_4400357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 3, 1, 2, 1, 3].length) (baseStart_4400357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4400357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4400357 prefixEnd_4400357 := by exact prefixLift 4400357
  have htrace : WordTrace (prefixWord ++ tailWord_4400357) baseStart_4400357 baseEnd_4400357 := by
    simpa [prefixWord, tailWord_4400357, baseEnd_4400357] using wordTrace_append hprefix tailTrace_4400357
  have hstable : (prefixWord ++ tailWord_4400357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4400357).length < 2 ^ (prefixWord ++ tailWord_4400357).sum := by decide
  have hdescent : baseEnd_4400357 < baseStart_4400357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4400357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4400363 : List Nat := [1, 1, 1, 1, 2, 6, 3, 1, 1, 4, 2]
def baseStart_4400363 : Nat := 118140960795 + 4400363 * 2 ^ 59
def prefixEnd_4400363 : Nat := 4983230072969 + 3 ^ 40 * 4400363 * 2
def baseEnd_4400363 : Nat := 2259501273260472293225605

theorem tailTrace_4400363 : CollatzResearch.WordTrace tailWord_4400363 prefixEnd_4400363 2259501273260472293225605 := by
  unfold tailWord_4400363
  simp only [CollatzResearch.WordTrace]
  refine ⟨160494423757243848013773743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106996282504829232009182495 160494423757243848013773743)
  ·
    refine ⟨240741635635865772020660615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160494423757243848013773743 240741635635865772020660615)
    ·
      refine ⟨361112453453798658030990923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240741635635865772020660615 361112453453798658030990923)
      ·
        refine ⟨541668680180697987046486385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 361112453453798658030990923 541668680180697987046486385)
        ·
          refine ⟨406251510135523490284864789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 541668680180697987046486385 406251510135523490284864789)
          ·
            refine ⟨19043039537602663607103037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 406251510135523490284864789 19043039537602663607103037)
            ·
              refine ⟨7141139826600998852663639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19043039537602663607103037 7141139826600998852663639)
              ·
                refine ⟨10711709739901498278995459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7141139826600998852663639 10711709739901498278995459)
                ·
                  refine ⟨16067564609852247418493189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10711709739901498278995459 16067564609852247418493189)
                  ·
                    refine ⟨3012668364347296390967473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16067564609852247418493189 3012668364347296390967473)
                    ·
                      refine ⟨2259501273260472293225605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3012668364347296390967473 2259501273260472293225605)
                      ·
                        rfl

theorem cell23_4400363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 1, 1, 4, 2].length) (baseStart_4400363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4400363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4400363 prefixEnd_4400363 := by exact prefixLift 4400363
  have htrace : WordTrace (prefixWord ++ tailWord_4400363) baseStart_4400363 baseEnd_4400363 := by
    simpa [prefixWord, tailWord_4400363, baseEnd_4400363] using wordTrace_append hprefix tailTrace_4400363
  have hstable : (prefixWord ++ tailWord_4400363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4400363).length < 2 ^ (prefixWord ++ tailWord_4400363).sum := by decide
  have hdescent : baseEnd_4400363 < baseStart_4400363 := by decide
  rcases family_descends (prefixWord ++ tailWord_4400363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4400366 : List Nat := [4, 1, 2, 1, 1, 1, 2, 2, 2, 4, 3]
def baseStart_4400366 : Nat := 118140960795 + 4400366 * 2 ^ 59
def prefixEnd_4400366 : Nat := 4983230072969 + 3 ^ 40 * 4400366 * 2
def baseEnd_4400366 : Nat := 2259502813702435781488091

theorem tailTrace_4400366 : CollatzResearch.WordTrace tailWord_4400366 prefixEnd_4400366 2259502813702435781488091 := by
  unfold tailWord_4400366
  simp only [CollatzResearch.WordTrace]
  refine ⟨20061816647029122440766619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106996355450821986350755301 20061816647029122440766619)
  ·
    refine ⟨30092724970543683661149929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20061816647029122440766619 30092724970543683661149929)
    ·
      refine ⟨22569543727907762745862447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30092724970543683661149929 22569543727907762745862447)
      ·
        refine ⟨33854315591861644118793671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22569543727907762745862447 33854315591861644118793671)
        ·
          refine ⟨50781473387792466178190507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33854315591861644118793671 50781473387792466178190507)
          ·
            refine ⟨76172210081688699267285761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50781473387792466178190507 76172210081688699267285761)
            ·
              refine ⟨57129157561266524450464321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76172210081688699267285761 57129157561266524450464321)
              ·
                refine ⟨42846868170949893337848241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57129157561266524450464321 42846868170949893337848241)
                ·
                  refine ⟨32135151128212420003386181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42846868170949893337848241 32135151128212420003386181)
                  ·
                    refine ⟨6025340836539828750634909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32135151128212420003386181 6025340836539828750634909)
                    ·
                      refine ⟨2259502813702435781488091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6025340836539828750634909 2259502813702435781488091)
                      ·
                        rfl

theorem cell23_4400366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 2, 4, 3].length) (baseStart_4400366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4400366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4400366 prefixEnd_4400366 := by exact prefixLift 4400366
  have htrace : WordTrace (prefixWord ++ tailWord_4400366) baseStart_4400366 baseEnd_4400366 := by
    simpa [prefixWord, tailWord_4400366, baseEnd_4400366] using wordTrace_append hprefix tailTrace_4400366
  have hstable : (prefixWord ++ tailWord_4400366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4400366).length < 2 ^ (prefixWord ++ tailWord_4400366).sum := by decide
  have hdescent : baseEnd_4400366 < baseStart_4400366 := by decide
  rcases family_descends (prefixWord ++ tailWord_4400366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4400433 : List Nat := [1, 2, 2, 3, 3, 2, 2, 1, 2, 5]
def baseStart_4400433 : Nat := 118140960795 + 4400433 * 2 ^ 59
def prefixEnd_4400433 : Nat := 4983230072969 + 3 ^ 40 * 4400433 * 2
def baseEnd_4400433 : Nat := 753179072302095673116761

theorem tailTrace_4400433 : CollatzResearch.WordTrace tailWord_4400433 prefixEnd_4400433 753179072302095673116761 := by
  unfold tailWord_4400433
  simp only [CollatzResearch.WordTrace]
  refine ⟨160496976866990249968821953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106997984577993499979214635 160496976866990249968821953)
  ·
    refine ⟨120372732650242687476616465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160496976866990249968821953 120372732650242687476616465)
    ·
      refine ⟨90279549487682015607462349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120372732650242687476616465 90279549487682015607462349)
      ·
        refine ⟨33854831057880755852798381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90279549487682015607462349 33854831057880755852798381)
        ·
          refine ⟨12695561646705283444799393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33854831057880755852798381 12695561646705283444799393)
          ·
            refine ⟨9521671235028962583599545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12695561646705283444799393 9521671235028962583599545)
            ·
              refine ⟨7141253426271721937699659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9521671235028962583599545 7141253426271721937699659)
              ·
                refine ⟨10711880139407582906549489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7141253426271721937699659 10711880139407582906549489)
                ·
                  refine ⟨8033910104555687179912117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10711880139407582906549489 8033910104555687179912117)
                  ·
                    refine ⟨753179072302095673116761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8033910104555687179912117 753179072302095673116761)
                    ·
                      rfl

theorem cell23_4400433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 1, 2, 5].length) (baseStart_4400433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4400433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4400433 prefixEnd_4400433 := by exact prefixLift 4400433
  have htrace : WordTrace (prefixWord ++ tailWord_4400433) baseStart_4400433 baseEnd_4400433 := by
    simpa [prefixWord, tailWord_4400433, baseEnd_4400433] using wordTrace_append hprefix tailTrace_4400433
  have hstable : (prefixWord ++ tailWord_4400433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4400433).length < 2 ^ (prefixWord ++ tailWord_4400433).sum := by decide
  have hdescent : baseEnd_4400433 < baseStart_4400433 := by decide
  rcases family_descends (prefixWord ++ tailWord_4400433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4400439 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 9]
def baseStart_4400439 : Nat := 118140960795 + 4400439 * 2 ^ 59
def prefixEnd_4400439 : Nat := 4983230072969 + 3 ^ 40 * 4400439 * 2
def baseEnd_4400439 : Nat := 2259540297790213995875255

theorem tailTrace_4400439 : CollatzResearch.WordTrace tailWord_4400439 prefixEnd_4400439 2259540297790213995875255 := by
  unfold tailWord_4400439
  simp only [CollatzResearch.WordTrace]
  refine ⟨160497195704968512993540371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106998130469979008662360247 160497195704968512993540371)
  ·
    refine ⟨240745793557452769490310557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160497195704968512993540371 240745793557452769490310557)
    ·
      refine ⟨90279672584044788558866459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 240745793557452769490310557 90279672584044788558866459)
      ·
        refine ⟨135419508876067182838299689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90279672584044788558866459 135419508876067182838299689)
        ·
          refine ⟨101564631657050387128724767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135419508876067182838299689 101564631657050387128724767)
          ·
            refine ⟨152346947485575580693087151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101564631657050387128724767 152346947485575580693087151)
            ·
              refine ⟨228520421228363371039630727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152346947485575580693087151 228520421228363371039630727)
              ·
                refine ⟨342780631842545056559446091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 228520421228363371039630727 342780631842545056559446091)
                ·
                  refine ⟨514170947763817584839169137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 342780631842545056559446091 514170947763817584839169137)
                  ·
                    refine ⟨385628210822863188629376853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 514170947763817584839169137 385628210822863188629376853)
                    ·
                      refine ⟨2259540297790213995875255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 385628210822863188629376853 2259540297790213995875255)
                      ·
                        rfl

theorem cell23_4400439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 9].length) (baseStart_4400439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4400439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4400439 prefixEnd_4400439 := by exact prefixLift 4400439
  have htrace : WordTrace (prefixWord ++ tailWord_4400439) baseStart_4400439 baseEnd_4400439 := by
    simpa [prefixWord, tailWord_4400439, baseEnd_4400439] using wordTrace_append hprefix tailTrace_4400439
  have hstable : (prefixWord ++ tailWord_4400439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4400439).length < 2 ^ (prefixWord ++ tailWord_4400439).sum := by decide
  have hdescent : baseEnd_4400439 < baseStart_4400439 := by decide
  rcases family_descends (prefixWord ++ tailWord_4400439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4400454 : List Nat := [6, 1, 1, 3, 1, 1, 1, 4, 5]
def baseStart_4400454 : Nat := 118140960795 + 4400454 * 2 ^ 59
def prefixEnd_4400454 : Nat := 4983230072969 + 3 ^ 40 * 4400454 * 2
def baseEnd_4400454 : Nat := 251060888888892381909743

theorem tailTrace_4400454 : CollatzResearch.WordTrace tailWord_4400454 prefixEnd_4400454 251060888888892381909743 := by
  unfold tailWord_4400454
  simp only [CollatzResearch.WordTrace]
  refine ⟨5015554462497317829854263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 106998495199942780370224277 5015554462497317829854263)
  ·
    refine ⟨7523331693745976744781395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5015554462497317829854263 7523331693745976744781395)
    ·
      refine ⟨11284997540618965117172093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7523331693745976744781395 11284997540618965117172093)
      ·
        refine ⟨4231874077732111918939535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11284997540618965117172093 4231874077732111918939535)
        ·
          refine ⟨6347811116598167878409303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4231874077732111918939535 6347811116598167878409303)
          ·
            refine ⟨9521716674897251817613955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6347811116598167878409303 9521716674897251817613955)
            ·
              refine ⟨14282575012345877726420933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9521716674897251817613955 14282575012345877726420933)
              ·
                refine ⟨2677982814814852073703925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14282575012345877726420933 2677982814814852073703925)
                ·
                  refine ⟨251060888888892381909743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2677982814814852073703925 251060888888892381909743)
                  ·
                    rfl

theorem cell23_4400454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_4400454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4400454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4400454 prefixEnd_4400454 := by exact prefixLift 4400454
  have htrace : WordTrace (prefixWord ++ tailWord_4400454) baseStart_4400454 baseEnd_4400454 := by
    simpa [prefixWord, tailWord_4400454, baseEnd_4400454] using wordTrace_append hprefix tailTrace_4400454
  have hstable : (prefixWord ++ tailWord_4400454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4400454).length < 2 ^ (prefixWord ++ tailWord_4400454).sum := by decide
  have hdescent : baseEnd_4400454 < baseStart_4400454 := by decide
  rcases family_descends (prefixWord ++ tailWord_4400454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4400456 : List Nat := [2, 1, 3, 1, 1, 2, 1, 2, 3, 4, 3]
def baseStart_4400456 : Nat := 118140960795 + 4400456 * 2 ^ 59
def prefixEnd_4400456 : Nat := 4983230072969 + 3 ^ 40 * 4400456 * 2
def baseEnd_4400456 : Nat := 2259549026961340429362677

theorem tailTrace_4400456 : CollatzResearch.WordTrace tailWord_4400456 prefixEnd_4400456 2259549026961340429362677 := by
  unfold tailWord_4400456
  simp only [CollatzResearch.WordTrace]
  refine ⟨80248907872953462448454611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106998543830604616597939481 80248907872953462448454611)
  ·
    refine ⟨120373361809430193672681917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80248907872953462448454611 120373361809430193672681917)
    ·
      refine ⟨45140010678536322627255719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120373361809430193672681917 45140010678536322627255719)
      ·
        refine ⟨67710016017804483940883579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45140010678536322627255719 67710016017804483940883579)
        ·
          refine ⟨101565024026706725911325369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67710016017804483940883579 101565024026706725911325369)
          ·
            refine ⟨76173768020030044433494027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101565024026706725911325369 76173768020030044433494027)
            ·
              refine ⟨114260652030045066650241041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76173768020030044433494027 114260652030045066650241041)
              ·
                refine ⟨85695489022533799987680781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114260652030045066650241041 85695489022533799987680781)
                ·
                  refine ⟨32135808383450174995380293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 85695489022533799987680781 32135808383450174995380293)
                  ·
                    refine ⟨6025464071896907811633805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32135808383450174995380293 6025464071896907811633805)
                    ·
                      refine ⟨2259549026961340429362677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6025464071896907811633805 2259549026961340429362677)
                      ·
                        rfl

theorem cell23_4400456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 3, 4, 3].length) (baseStart_4400456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4400456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4400456 prefixEnd_4400456 := by exact prefixLift 4400456
  have htrace : WordTrace (prefixWord ++ tailWord_4400456) baseStart_4400456 baseEnd_4400456 := by
    simpa [prefixWord, tailWord_4400456, baseEnd_4400456] using wordTrace_append hprefix tailTrace_4400456
  have hstable : (prefixWord ++ tailWord_4400456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4400456).length < 2 ^ (prefixWord ++ tailWord_4400456).sum := by decide
  have hdescent : baseEnd_4400456 < baseStart_4400456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4400456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4400459 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 12]
def baseStart_4400459 : Nat := 118140960795 + 4400459 * 2 ^ 59
def prefixEnd_4400459 : Nat := 4983230072969 + 3 ^ 40 * 4400459 * 2
def baseEnd_4400459 : Nat := 251061174155922657513907

theorem tailTrace_4400459 : CollatzResearch.WordTrace tailWord_4400459 prefixEnd_4400459 251061174155922657513907 := by
  unfold tailWord_4400459
  simp only [CollatzResearch.WordTrace]
  refine ⟨160497925164896056409268431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106998616776597370939512287 160497925164896056409268431)
  ·
    refine ⟨240746887747344084613902647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160497925164896056409268431 240746887747344084613902647)
    ·
      refine ⟨361120331621016126920853971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240746887747344084613902647 361120331621016126920853971)
      ·
        refine ⟨541680497431524190381280957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 361120331621016126920853971 541680497431524190381280957)
        ·
          refine ⟨203130186536821571392980359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 541680497431524190381280957 203130186536821571392980359)
          ·
            refine ⟨304695279805232357089470539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203130186536821571392980359 304695279805232357089470539)
            ·
              refine ⟨457042919707848535634205809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 304695279805232357089470539 457042919707848535634205809)
              ·
                refine ⟨342782189780886401725654357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 457042919707848535634205809 342782189780886401725654357)
                ·
                  refine ⟨251061174155922657513907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 342782189780886401725654357 251061174155922657513907)
                  ·
                    rfl

theorem cell23_4400459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 12].length) (baseStart_4400459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4400459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4400459 prefixEnd_4400459 := by exact prefixLift 4400459
  have htrace : WordTrace (prefixWord ++ tailWord_4400459) baseStart_4400459 baseEnd_4400459 := by
    simpa [prefixWord, tailWord_4400459, baseEnd_4400459] using wordTrace_append hprefix tailTrace_4400459
  have hstable : (prefixWord ++ tailWord_4400459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4400459).length < 2 ^ (prefixWord ++ tailWord_4400459).sum := by decide
  have hdescent : baseEnd_4400459 < baseStart_4400459 := by decide
  rcases family_descends (prefixWord ++ tailWord_4400459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4400466 : List Nat := [3, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4]
def baseStart_4400466 : Nat := 118140960795 + 4400466 * 2 ^ 59
def prefixEnd_4400466 : Nat := 4983230072969 + 3 ^ 40 * 4400466 * 2
def baseEnd_4400466 : Nat := 2259554161767885390237631

theorem tailTrace_4400466 : CollatzResearch.WordTrace tailWord_4400466 prefixEnd_4400466 2259554161767885390237631 := by
  unfold tailWord_4400466
  simp only [CollatzResearch.WordTrace]
  refine ⟨40124545118967674151193313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106998786983913797736515501 40124545118967674151193313)
  ·
    refine ⟨30093408839225755613394985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40124545118967674151193313 30093408839225755613394985)
    ·
      refine ⟨22570056629419316710046239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30093408839225755613394985 22570056629419316710046239)
      ·
        refine ⟨33855084944128975065069359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22570056629419316710046239 33855084944128975065069359)
        ·
          refine ⟨50782627416193462597604039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33855084944128975065069359 50782627416193462597604039)
          ·
            refine ⟨76173941124290193896406059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50782627416193462597604039 76173941124290193896406059)
            ·
              refine ⟨114260911686435290844609089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76173941124290193896406059 114260911686435290844609089)
              ·
                refine ⟨85695683764826468133456817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114260911686435290844609089 85695683764826468133456817)
                ·
                  refine ⟨64271762823619851100092613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85695683764826468133456817 64271762823619851100092613)
                  ·
                    refine ⟨12050955529428722081267365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 64271762823619851100092613 12050955529428722081267365)
                    ·
                      refine ⟨2259554161767885390237631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12050955529428722081267365 2259554161767885390237631)
                      ·
                        rfl

theorem cell23_4400466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_4400466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4400466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4400466 prefixEnd_4400466 := by exact prefixLift 4400466
  have htrace : WordTrace (prefixWord ++ tailWord_4400466) baseStart_4400466 baseEnd_4400466 := by
    simpa [prefixWord, tailWord_4400466, baseEnd_4400466] using wordTrace_append hprefix tailTrace_4400466
  have hstable : (prefixWord ++ tailWord_4400466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4400466).length < 2 ^ (prefixWord ++ tailWord_4400466).sum := by decide
  have hdescent : baseEnd_4400466 < baseStart_4400466 := by decide
  rcases family_descends (prefixWord ++ tailWord_4400466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4400487 : List Nat := [1, 1, 5, 1, 5, 1, 1, 1, 2, 1, 4]
def baseStart_4400487 : Nat := 118140960795 + 4400487 * 2 ^ 59
def prefixEnd_4400487 : Nat := 4983230072969 + 3 ^ 40 * 4400487 * 2
def baseEnd_4400487 : Nat := 2259564944861629808075035

theorem tailTrace_4400487 : CollatzResearch.WordTrace tailWord_4400487 prefixEnd_4400487 2259564944861629808075035 := by
  unfold tailWord_4400487
  simp only [CollatzResearch.WordTrace]
  refine ⟨160498946408794617191287715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106999297605863078127525143 160498946408794617191287715)
  ·
    refine ⟨240748419613191925786931573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160498946408794617191287715 240748419613191925786931573)
    ·
      refine ⟨22570164338736743042524835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 240748419613191925786931573 22570164338736743042524835)
      ·
        refine ⟨33855246508105114563787253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22570164338736743042524835 33855246508105114563787253)
        ·
          refine ⟨3173929360134854490355055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33855246508105114563787253 3173929360134854490355055)
          ·
            refine ⟨4760894040202281735532583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3173929360134854490355055 4760894040202281735532583)
            ·
              refine ⟨7141341060303422603298875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4760894040202281735532583 7141341060303422603298875)
              ·
                refine ⟨10712011590455133904948313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7141341060303422603298875 10712011590455133904948313)
                ·
                  refine ⟨8034008692841350428711235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10712011590455133904948313 8034008692841350428711235)
                  ·
                    refine ⟨12051013039262025643066853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8034008692841350428711235 12051013039262025643066853)
                    ·
                      refine ⟨2259564944861629808075035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12051013039262025643066853 2259564944861629808075035)
                      ·
                        rfl

theorem cell23_4400487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 1, 2, 1, 4].length) (baseStart_4400487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4400487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4400487 prefixEnd_4400487 := by exact prefixLift 4400487
  have htrace : WordTrace (prefixWord ++ tailWord_4400487) baseStart_4400487 baseEnd_4400487 := by
    simpa [prefixWord, tailWord_4400487, baseEnd_4400487] using wordTrace_append hprefix tailTrace_4400487
  have hstable : (prefixWord ++ tailWord_4400487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4400487).length < 2 ^ (prefixWord ++ tailWord_4400487).sum := by decide
  have hdescent : baseEnd_4400487 < baseStart_4400487 := by decide
  rcases family_descends (prefixWord ++ tailWord_4400487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4400490 : List Nat := [3, 1, 3, 3, 2, 1, 1, 1, 1, 4, 3]
def baseStart_4400490 : Nat := 118140960795 + 4400490 * 2 ^ 59
def prefixEnd_4400490 : Nat := 4983230072969 + 3 ^ 40 * 4400490 * 2
def baseEnd_4400490 : Nat := 2259566485303593296337521

theorem tailTrace_4400490 : CollatzResearch.WordTrace tailWord_4400490 prefixEnd_4400490 2259566485303593296337521 := by
  unfold tailWord_4400490
  simp only [CollatzResearch.WordTrace]
  refine ⟨40124763956945937175911731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106999370551855832469097949 40124763956945937175911731)
  ·
    refine ⟨60187145935418905763867597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40124763956945937175911731 60187145935418905763867597)
    ·
      refine ⟨22570179725782089661450349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60187145935418905763867597 22570179725782089661450349)
      ·
        refine ⟨8463817397168283623043881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22570179725782089661450349 8463817397168283623043881)
        ·
          refine ⟨6347863047876212717282911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8463817397168283623043881 6347863047876212717282911)
          ·
            refine ⟨9521794571814319075924367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6347863047876212717282911 9521794571814319075924367)
            ·
              refine ⟨14282691857721478613886551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9521794571814319075924367 14282691857721478613886551)
              ·
                refine ⟨21424037786582217920829827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14282691857721478613886551 21424037786582217920829827)
                ·
                  refine ⟨32136056679873326881244741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21424037786582217920829827 32136056679873326881244741)
                  ·
                    refine ⟨6025510627476248790233389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32136056679873326881244741 6025510627476248790233389)
                    ·
                      refine ⟨2259566485303593296337521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6025510627476248790233389 2259566485303593296337521)
                      ·
                        rfl

theorem cell23_4400490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_4400490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4400490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4400490 prefixEnd_4400490 := by exact prefixLift 4400490
  have htrace : WordTrace (prefixWord ++ tailWord_4400490) baseStart_4400490 baseEnd_4400490 := by
    simpa [prefixWord, tailWord_4400490, baseEnd_4400490] using wordTrace_append hprefix tailTrace_4400490
  have hstable : (prefixWord ++ tailWord_4400490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4400490).length < 2 ^ (prefixWord ++ tailWord_4400490).sum := by decide
  have hdescent : baseEnd_4400490 < baseStart_4400490 := by decide
  rcases family_descends (prefixWord ++ tailWord_4400490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4400503 : List Nat := [1, 1, 3, 1, 1, 2, 3, 2, 5, 1, 3]
def baseStart_4400503 : Nat := 118140960795 + 4400503 * 2 ^ 59
def prefixEnd_4400503 : Nat := 4983230072969 + 3 ^ 40 * 4400503 * 2
def baseEnd_4400503 : Nat := 2259573160552101745474961

theorem tailTrace_4400503 : CollatzResearch.WordTrace tailWord_4400503 prefixEnd_4400503 2259573160552101745474961 := by
  unfold tailWord_4400503
  simp only [CollatzResearch.WordTrace]
  refine ⟨160499529976736651923870163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106999686651157767949246775 160499529976736651923870163)
  ·
    refine ⟨240749294965104977885805245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160499529976736651923870163 240749294965104977885805245)
    ·
      refine ⟨90280985611914366707176967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 240749294965104977885805245 90280985611914366707176967)
      ·
        refine ⟨135421478417871550060765451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90280985611914366707176967 135421478417871550060765451)
        ·
          refine ⟨203132217626807325091148177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135421478417871550060765451 203132217626807325091148177)
          ·
            refine ⟨152349163220105493818361133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 203132217626807325091148177 152349163220105493818361133)
            ·
              refine ⟨57130936207539560181885425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 152349163220105493818361133 57130936207539560181885425)
              ·
                refine ⟨42848202155654670136414069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57130936207539560181885425 42848202155654670136414069)
                ·
                  refine ⟨4017018952092625325288819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42848202155654670136414069 4017018952092625325288819)
                  ·
                    refine ⟨6025528428138937987933229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4017018952092625325288819 6025528428138937987933229)
                    ·
                      refine ⟨2259573160552101745474961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6025528428138937987933229 2259573160552101745474961)
                      ·
                        rfl

theorem cell23_4400503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 5, 1, 3].length) (baseStart_4400503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4400503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4400503 prefixEnd_4400503 := by exact prefixLift 4400503
  have htrace : WordTrace (prefixWord ++ tailWord_4400503) baseStart_4400503 baseEnd_4400503 := by
    simpa [prefixWord, tailWord_4400503, baseEnd_4400503] using wordTrace_append hprefix tailTrace_4400503
  have hstable : (prefixWord ++ tailWord_4400503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4400503).length < 2 ^ (prefixWord ++ tailWord_4400503).sum := by decide
  have hdescent : baseEnd_4400503 < baseStart_4400503 := by decide
  rcases family_descends (prefixWord ++ tailWord_4400503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4400514 : List Nat := [3, 4, 2, 1, 1, 1, 2, 4, 1, 4]
def baseStart_4400514 : Nat := 118140960795 + 4400514 * 2 ^ 59
def prefixEnd_4400514 : Nat := 4983230072969 + 3 ^ 40 * 4400514 * 2
def baseEnd_4400514 : Nat := 753192936279767067479137

theorem tailTrace_4400514 : CollatzResearch.WordTrace tailWord_4400514 prefixEnd_4400514 753192936279767067479137 := by
  unfold tailWord_4400514
  simp only [CollatzResearch.WordTrace]
  refine ⟨40124982794924200200630149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106999954119797867201680397 40124982794924200200630149)
  ·
    refine ⟨7523434274048287537618153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40124982794924200200630149 7523434274048287537618153)
    ·
      refine ⟨5642575705536215653213615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7523434274048287537618153 5642575705536215653213615)
      ·
        refine ⟨8463863558304323479820423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5642575705536215653213615 8463863558304323479820423)
        ·
          refine ⟨12695795337456485219730635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8463863558304323479820423 12695795337456485219730635)
          ·
            refine ⟨19043693006184727829595953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12695795337456485219730635 19043693006184727829595953)
            ·
              refine ⟨14282769754638545872196965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19043693006184727829595953 14282769754638545872196965)
              ·
                refine ⟨2678019328994727351036931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14282769754638545872196965 2678019328994727351036931)
                ·
                  refine ⟨4017028993492091026555397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2678019328994727351036931 4017028993492091026555397)
                  ·
                    refine ⟨753192936279767067479137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4017028993492091026555397 753192936279767067479137)
                    ·
                      rfl

theorem cell23_4400514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_4400514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4400514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4400514 prefixEnd_4400514 := by exact prefixLift 4400514
  have htrace : WordTrace (prefixWord ++ tailWord_4400514) baseStart_4400514 baseEnd_4400514 := by
    simpa [prefixWord, tailWord_4400514, baseEnd_4400514] using wordTrace_append hprefix tailTrace_4400514
  have hstable : (prefixWord ++ tailWord_4400514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4400514).length < 2 ^ (prefixWord ++ tailWord_4400514).sum := by decide
  have hdescent : baseEnd_4400514 < baseStart_4400514 := by decide
  rcases family_descends (prefixWord ++ tailWord_4400514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4400520 : List Nat := [2, 1, 3, 3, 1, 2, 1, 3, 3, 1, 3]
def baseStart_4400520 : Nat := 118140960795 + 4400520 * 2 ^ 59
def prefixEnd_4400520 : Nat := 4983230072969 + 3 ^ 40 * 4400520 * 2
def baseEnd_4400520 : Nat := 2259581889723228178962383

theorem tailTrace_4400520 : CollatzResearch.WordTrace tailWord_4400520 prefixEnd_4400520 2259581889723228178962383 := by
  unfold tailWord_4400520
  simp only [CollatzResearch.WordTrace]
  refine ⟨80250075008837531913619507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107000100011783375884826009 80250075008837531913619507)
  ·
    refine ⟨120375112513256297870429261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80250075008837531913619507 120375112513256297870429261)
    ·
      refine ⟨45140667192471111701410973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120375112513256297870429261 45140667192471111701410973)
      ·
        refine ⟨16927750197176666888029115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45140667192471111701410973 16927750197176666888029115)
        ·
          refine ⟨25391625295765000332043673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16927750197176666888029115 25391625295765000332043673)
          ·
            refine ⟨19043718971823750249032755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25391625295765000332043673 19043718971823750249032755)
            ·
              refine ⟨28565578457735625373549133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19043718971823750249032755 28565578457735625373549133)
              ·
                refine ⟨10712091921650859515080925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28565578457735625373549133 10712091921650859515080925)
                ·
                  refine ⟨4017034470619072318155347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10712091921650859515080925 4017034470619072318155347)
                  ·
                    refine ⟨6025551705928608477233021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4017034470619072318155347 6025551705928608477233021)
                    ·
                      refine ⟨2259581889723228178962383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6025551705928608477233021 2259581889723228178962383)
                      ·
                        rfl

theorem cell23_4400520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_4400520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4400520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4400520 prefixEnd_4400520 := by exact prefixLift 4400520
  have htrace : WordTrace (prefixWord ++ tailWord_4400520) baseStart_4400520 baseEnd_4400520 := by
    simpa [prefixWord, tailWord_4400520, baseEnd_4400520] using wordTrace_append hprefix tailTrace_4400520
  have hstable : (prefixWord ++ tailWord_4400520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4400520).length < 2 ^ (prefixWord ++ tailWord_4400520).sum := by decide
  have hdescent : baseEnd_4400520 < baseStart_4400520 := by decide
  rcases family_descends (prefixWord ++ tailWord_4400520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4400578 : List Nat := [3, 5, 2, 1, 1, 2, 2, 1, 6]
def baseStart_4400578 : Nat := 118140960795 + 4400578 * 2 ^ 59
def prefixEnd_4400578 : Nat := 4983230072969 + 3 ^ 40 * 4400578 * 2
def baseEnd_4400578 : Nat := 251067963511243216893013

theorem tailTrace_4400578 : CollatzResearch.WordTrace tailWord_4400578 prefixEnd_4400578 251067963511243216893013 := by
  unfold tailWord_4400578
  simp only [CollatzResearch.WordTrace]
  refine ⟨40125566362866234933212597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107001510300976626488566925 40125566362866234933212597)
  ·
    refine ⟨3761771846518709524988681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40125566362866234933212597 3761771846518709524988681)
    ·
      refine ⟨2821328884889032143741511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3761771846518709524988681 2821328884889032143741511)
      ·
        refine ⟨4231993327333548215612267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2821328884889032143741511 4231993327333548215612267)
        ·
          refine ⟨6347989991000322323418401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4231993327333548215612267 6347989991000322323418401)
          ·
            refine ⟨4760992493250241742563801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6347989991000322323418401 4760992493250241742563801)
            ·
              refine ⟨3570744369937681306922851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4760992493250241742563801 3570744369937681306922851)
              ·
                refine ⟨5356116554906521960384277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3570744369937681306922851 5356116554906521960384277)
                ·
                  refine ⟨251067963511243216893013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5356116554906521960384277 251067963511243216893013)
                  ·
                    rfl

theorem cell23_4400578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_4400578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4400578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4400578 prefixEnd_4400578 := by exact prefixLift 4400578
  have htrace : WordTrace (prefixWord ++ tailWord_4400578) baseStart_4400578 baseEnd_4400578 := by
    simpa [prefixWord, tailWord_4400578, baseEnd_4400578] using wordTrace_append hprefix tailTrace_4400578
  have hstable : (prefixWord ++ tailWord_4400578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4400578).length < 2 ^ (prefixWord ++ tailWord_4400578).sum := by decide
  have hdescent : baseEnd_4400578 < baseStart_4400578 := by decide
  rcases family_descends (prefixWord ++ tailWord_4400578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4400580 : List Nat := [2, 3, 3, 2, 1, 1, 2, 2, 1, 1, 5]
def baseStart_4400580 : Nat := 118140960795 + 4400580 * 2 ^ 59
def prefixEnd_4400580 : Nat := 4983230072969 + 3 ^ 40 * 4400580 * 2
def baseEnd_4400580 : Nat := 2259612698562497944212107

theorem tailTrace_4400580 : CollatzResearch.WordTrace tailWord_4400580 prefixEnd_4400580 2259612698562497944212107 := by
  unfold tailWord_4400580
  simp only [CollatzResearch.WordTrace]
  refine ⟨80251169198728847037211597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107001558931638462716282129 80251169198728847037211597)
  ·
    refine ⟨30094188449523317638954349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80251169198728847037211597 30094188449523317638954349)
    ·
      refine ⟨11285320668571244114607881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30094188449523317638954349 11285320668571244114607881)
      ·
        refine ⟨8463990501428433085955911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11285320668571244114607881 8463990501428433085955911)
        ·
          refine ⟨12695985752142649628933867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8463990501428433085955911 12695985752142649628933867)
          ·
            refine ⟨19043978628213974443400801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12695985752142649628933867 19043978628213974443400801)
            ·
              refine ⟨14282983971160480832550601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19043978628213974443400801 14282983971160480832550601)
              ·
                refine ⟨10712237978370360624412951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14282983971160480832550601 10712237978370360624412951)
                ·
                  refine ⟨16068356967555540936619427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10712237978370360624412951 16068356967555540936619427)
                  ·
                    refine ⟨24102535451333311404929141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16068356967555540936619427 24102535451333311404929141)
                    ·
                      refine ⟨2259612698562497944212107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24102535451333311404929141 2259612698562497944212107)
                      ·
                        rfl

theorem cell23_4400580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_4400580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4400580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4400580 prefixEnd_4400580 := by exact prefixLift 4400580
  have htrace : WordTrace (prefixWord ++ tailWord_4400580) baseStart_4400580 baseEnd_4400580 := by
    simpa [prefixWord, tailWord_4400580, baseEnd_4400580] using wordTrace_append hprefix tailTrace_4400580
  have hstable : (prefixWord ++ tailWord_4400580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4400580).length < 2 ^ (prefixWord ++ tailWord_4400580).sum := by decide
  have hdescent : baseEnd_4400580 < baseStart_4400580 := by decide
  rcases family_descends (prefixWord ++ tailWord_4400580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4400603 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 3, 9, 2]
def baseStart_4400603 : Nat := 118140960795 + 4400603 * 2 ^ 59
def prefixEnd_4400603 : Nat := 4983230072969 + 3 ^ 40 * 4400603 * 2
def baseEnd_4400603 : Nat := 2259624508617551354224501

theorem tailTrace_4400603 : CollatzResearch.WordTrace tailWord_4400603 prefixEnd_4400603 2259624508617551354224501 := by
  unfold tailWord_4400603
  simp only [CollatzResearch.WordTrace]
  refine ⟨160503177276374369002510463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107002118184249579335006975 160503177276374369002510463)
  ·
    refine ⟨240754765914561553503765695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160503177276374369002510463 240754765914561553503765695)
    ·
      refine ⟨361132148871842330255648543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240754765914561553503765695 361132148871842330255648543)
      ·
        refine ⟨541698223307763495383472815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 361132148871842330255648543 541698223307763495383472815)
        ·
          refine ⟨812547334961645243075209223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 541698223307763495383472815 812547334961645243075209223)
          ·
            refine ⟨1218821002442467864612813835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 812547334961645243075209223 1218821002442467864612813835)
            ·
              refine ⟨1828231503663701796919220753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1218821002442467864612813835 1828231503663701796919220753)
              ·
                refine ⟨1371173627747776347689415565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1828231503663701796919220753 1371173627747776347689415565)
                ·
                  refine ⟨514190110405416130383530837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1371173627747776347689415565 514190110405416130383530837)
                  ·
                    refine ⟨3012832678156735138966001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 514190110405416130383530837 3012832678156735138966001)
                    ·
                      refine ⟨2259624508617551354224501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3012832678156735138966001 2259624508617551354224501)
                      ·
                        rfl

theorem cell23_4400603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 9, 2].length) (baseStart_4400603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4400603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4400603 prefixEnd_4400603 := by exact prefixLift 4400603
  have htrace : WordTrace (prefixWord ++ tailWord_4400603) baseStart_4400603 baseEnd_4400603 := by
    simpa [prefixWord, tailWord_4400603, baseEnd_4400603] using wordTrace_append hprefix tailTrace_4400603
  have hstable : (prefixWord ++ tailWord_4400603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4400603).length < 2 ^ (prefixWord ++ tailWord_4400603).sum := by decide
  have hdescent : baseEnd_4400603 < baseStart_4400603 := by decide
  rcases family_descends (prefixWord ++ tailWord_4400603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4400701 : List Nat := [1, 4, 1, 3, 4, 1, 1, 1, 1, 4, 2]
def baseStart_4400701 : Nat := 118140960795 + 4400701 * 2 ^ 59
def prefixEnd_4400701 : Nat := 4983230072969 + 3 ^ 40 * 4400701 * 2
def baseEnd_4400701 : Nat := 2259674829721691970799051

theorem tailTrace_4400701 : CollatzResearch.WordTrace tailWord_4400701 prefixEnd_4400701 2259674829721691970799051 := by
  unfold tailWord_4400701
  simp only [CollatzResearch.WordTrace]
  refine ⟨160506751630019331739577957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107004501086679554493051971 160506751630019331739577957)
  ·
    refine ⟨30095015930628624701170867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 160506751630019331739577957 30095015930628624701170867)
    ·
      refine ⟨45142523895942937051756301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30095015930628624701170867 45142523895942937051756301)
      ·
        refine ⟨16928446460978601394408613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45142523895942937051756301 16928446460978601394408613)
        ·
          refine ⟨3174083711433487761451615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16928446460978601394408613 3174083711433487761451615)
          ·
            refine ⟨4761125567150231642177423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3174083711433487761451615 4761125567150231642177423)
            ·
              refine ⟨7141688350725347463266135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4761125567150231642177423 7141688350725347463266135)
              ·
                refine ⟨10712532526088021194899203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7141688350725347463266135 10712532526088021194899203)
                ·
                  refine ⟨16068798789132031792348805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10712532526088021194899203 16068798789132031792348805)
                  ·
                    refine ⟨3012899772962255961065401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16068798789132031792348805 3012899772962255961065401)
                    ·
                      refine ⟨2259674829721691970799051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3012899772962255961065401 2259674829721691970799051)
                      ·
                        rfl

theorem cell23_4400701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 1, 1, 4, 2].length) (baseStart_4400701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4400701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4400701 prefixEnd_4400701 := by exact prefixLift 4400701
  have htrace : WordTrace (prefixWord ++ tailWord_4400701) baseStart_4400701 baseEnd_4400701 := by
    simpa [prefixWord, tailWord_4400701, baseEnd_4400701] using wordTrace_append hprefix tailTrace_4400701
  have hstable : (prefixWord ++ tailWord_4400701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4400701).length < 2 ^ (prefixWord ++ tailWord_4400701).sum := by decide
  have hdescent : baseEnd_4400701 < baseStart_4400701 := by decide
  rcases family_descends (prefixWord ++ tailWord_4400701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4400703 : List Nat := [1, 1, 2, 2, 3, 3, 1, 2, 1, 7]
def baseStart_4400703 : Nat := 118140960795 + 4400703 * 2 ^ 59
def prefixEnd_4400703 : Nat := 4983230072969 + 3 ^ 40 * 4400703 * 2
def baseEnd_4400703 : Nat := 753225285561000320991347

theorem tailTrace_4400703 : CollatzResearch.WordTrace tailWord_4400703 prefixEnd_4400703 753225285561000320991347 := by
  unfold tailWord_4400703
  simp only [CollatzResearch.WordTrace]
  refine ⟨160506824576012086081150763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107004549717341390720767175 160506824576012086081150763)
  ·
    refine ⟨240760236864018129121726145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160506824576012086081150763 240760236864018129121726145)
    ·
      refine ⟨180570177648013596841294609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 240760236864018129121726145 180570177648013596841294609)
      ·
        refine ⟨135427633236010197630970957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180570177648013596841294609 135427633236010197630970957)
        ·
          refine ⟨50785362463503824111614109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135427633236010197630970957 50785362463503824111614109)
          ·
            refine ⟨19044510923813934041855291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50785362463503824111614109 19044510923813934041855291)
            ·
              refine ⟨28566766385720901062782937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19044510923813934041855291 28566766385720901062782937)
              ·
                refine ⟨21425074789290675797087203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28566766385720901062782937 21425074789290675797087203)
                ·
                  refine ⟨32137612183936013695630805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21425074789290675797087203 32137612183936013695630805)
                  ·
                    refine ⟨753225285561000320991347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32137612183936013695630805 753225285561000320991347)
                    ·
                      rfl

theorem cell23_4400703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 7].length) (baseStart_4400703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4400703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4400703 prefixEnd_4400703 := by exact prefixLift 4400703
  have htrace : WordTrace (prefixWord ++ tailWord_4400703) baseStart_4400703 baseEnd_4400703 := by
    simpa [prefixWord, tailWord_4400703, baseEnd_4400703] using wordTrace_append hprefix tailTrace_4400703
  have hstable : (prefixWord ++ tailWord_4400703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4400703).length < 2 ^ (prefixWord ++ tailWord_4400703).sum := by decide
  have hdescent : baseEnd_4400703 < baseStart_4400703 := by decide
  rcases family_descends (prefixWord ++ tailWord_4400703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4400740 : List Nat := [2, 3, 1, 1, 2, 3, 1, 1, 4, 1, 4]
def baseStart_4400740 : Nat := 118140960795 + 4400740 * 2 ^ 59
def prefixEnd_4400740 : Nat := 4983230072969 + 3 ^ 40 * 4400740 * 2
def baseEnd_4400740 : Nat := 2259694855467217318211371

theorem tailTrace_4400740 : CollatzResearch.WordTrace tailWord_4400740 prefixEnd_4400740 2259694855467217318211371 := by
  unfold tailWord_4400740
  simp only [CollatzResearch.WordTrace]
  refine ⟨80254087038439020700123837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107005449384585360933498449 80254087038439020700123837)
  ·
    refine ⟨30095282639414632762546439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80254087038439020700123837 30095282639414632762546439)
    ·
      refine ⟨45142923959121949143819659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30095282639414632762546439 45142923959121949143819659)
      ·
        refine ⟨67714385938682923715729489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45142923959121949143819659 67714385938682923715729489)
        ·
          refine ⟨50785789454012192786797117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67714385938682923715729489 50785789454012192786797117)
          ·
            refine ⟨19044671045254572295048919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50785789454012192786797117 19044671045254572295048919)
            ·
              refine ⟨28567006567881858442573379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19044671045254572295048919 28567006567881858442573379)
              ·
                refine ⟨42850509851822787663860069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28567006567881858442573379 42850509851822787663860069)
                ·
                  refine ⟨8034470597216772686973763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42850509851822787663860069 8034470597216772686973763)
                  ·
                    refine ⟨12051705895825159030460645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8034470597216772686973763 12051705895825159030460645)
                    ·
                      refine ⟨2259694855467217318211371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12051705895825159030460645 2259694855467217318211371)
                      ·
                        rfl

theorem cell23_4400740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 4, 1, 4].length) (baseStart_4400740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4400740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4400740 prefixEnd_4400740 := by exact prefixLift 4400740
  have htrace : WordTrace (prefixWord ++ tailWord_4400740) baseStart_4400740 baseEnd_4400740 := by
    simpa [prefixWord, tailWord_4400740, baseEnd_4400740] using wordTrace_append hprefix tailTrace_4400740
  have hstable : (prefixWord ++ tailWord_4400740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4400740).length < 2 ^ (prefixWord ++ tailWord_4400740).sum := by decide
  have hdescent : baseEnd_4400740 < baseStart_4400740 := by decide
  rcases family_descends (prefixWord ++ tailWord_4400740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4400753 : List Nat := [1, 2, 2, 2, 1, 1, 1, 4, 2, 1, 6]
def baseStart_4400753 : Nat := 118140960795 + 4400753 * 2 ^ 59
def prefixEnd_4400753 : Nat := 4983230072969 + 3 ^ 40 * 4400753 * 2
def baseEnd_4400753 : Nat := 2259701530715725767348811

theorem tailTrace_4400753 : CollatzResearch.WordTrace tailWord_4400753 prefixEnd_4400753 2259701530715725767348811 := by
  unfold tailWord_4400753
  simp only [CollatzResearch.WordTrace]
  refine ⟨160508648225830944620470913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107005765483887296413647275 160508648225830944620470913)
  ·
    refine ⟨120381486169373208465353185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160508648225830944620470913 120381486169373208465353185)
    ·
      refine ⟨90286114627029906349014889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120381486169373208465353185 90286114627029906349014889)
      ·
        refine ⟨67714585970272429761761167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90286114627029906349014889 67714585970272429761761167)
        ·
          refine ⟨101571878955408644642641751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67714585970272429761761167 101571878955408644642641751)
          ·
            refine ⟨152357818433112966963962627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101571878955408644642641751 152357818433112966963962627)
            ·
              refine ⟨228536727649669450445943941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152357818433112966963962627 228536727649669450445943941)
              ·
                refine ⟨42850636434313021958614489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 228536727649669450445943941 42850636434313021958614489)
                ·
                  refine ⟨32137977325734766468960867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42850636434313021958614489 32137977325734766468960867)
                  ·
                    refine ⟨48206965988602149703441301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32137977325734766468960867 48206965988602149703441301)
                    ·
                      refine ⟨2259701530715725767348811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48206965988602149703441301 2259701530715725767348811)
                      ·
                        rfl

theorem cell23_4400753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_4400753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4400753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4400753 prefixEnd_4400753 := by exact prefixLift 4400753
  have htrace : WordTrace (prefixWord ++ tailWord_4400753) baseStart_4400753 baseEnd_4400753 := by
    simpa [prefixWord, tailWord_4400753, baseEnd_4400753] using wordTrace_append hprefix tailTrace_4400753
  have hstable : (prefixWord ++ tailWord_4400753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4400753).length < 2 ^ (prefixWord ++ tailWord_4400753).sum := by decide
  have hdescent : baseEnd_4400753 < baseStart_4400753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4400753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4400801 : List Nat := [1, 2, 3, 3, 2, 1, 4, 2, 1, 4]
def baseStart_4400801 : Nat := 118140960795 + 4400801 * 2 ^ 59
def prefixEnd_4400801 : Nat := 4983230072969 + 3 ^ 40 * 4400801 * 2
def baseEnd_4400801 : Nat := 753242059262380526516197

theorem tailTrace_4400801 : CollatzResearch.WordTrace tailWord_4400801 prefixEnd_4400801 753242059262380526516197 := by
  unfold tailWord_4400801
  simp only [CollatzResearch.WordTrace]
  refine ⟨160510398929657048818218257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107006932619771365878812171 160510398929657048818218257)
  ·
    refine ⟨120382799197242786613663693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160510398929657048818218257 120382799197242786613663693)
    ·
      refine ⟨45143549698966044980123885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120382799197242786613663693 45143549698966044980123885)
      ·
        refine ⟨16928831137112266867546457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45143549698966044980123885 16928831137112266867546457)
        ·
          refine ⟨12696623352834200150659843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16928831137112266867546457 12696623352834200150659843)
          ·
            refine ⟨19044935029251300225989765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12696623352834200150659843 19044935029251300225989765)
            ·
              refine ⟨3570925317984618792373081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19044935029251300225989765 3570925317984618792373081)
              ·
                refine ⟨2678193988488464094279811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3570925317984618792373081 2678193988488464094279811)
                ·
                  refine ⟨4017290982732696141419717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2678193988488464094279811 4017290982732696141419717)
                  ·
                    refine ⟨753242059262380526516197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4017290982732696141419717 753242059262380526516197)
                    ·
                      rfl

theorem cell23_4400801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 4, 2, 1, 4].length) (baseStart_4400801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4400801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4400801 prefixEnd_4400801 := by exact prefixLift 4400801
  have htrace : WordTrace (prefixWord ++ tailWord_4400801) baseStart_4400801 baseEnd_4400801 := by
    simpa [prefixWord, tailWord_4400801, baseEnd_4400801] using wordTrace_append hprefix tailTrace_4400801
  have hstable : (prefixWord ++ tailWord_4400801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4400801).length < 2 ^ (prefixWord ++ tailWord_4400801).sum := by decide
  have hdescent : baseEnd_4400801 < baseStart_4400801 := by decide
  rcases family_descends (prefixWord ++ tailWord_4400801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4400808 : List Nat := [2, 1, 7, 1, 1, 1, 1, 1, 2, 4, 2]
def baseStart_4400808 : Nat := 118140960795 + 4400808 * 2 ^ 59
def prefixEnd_4400808 : Nat := 4983230072969 + 3 ^ 40 * 4400808 * 2
def baseEnd_4400808 : Nat := 2259729772151723052161059

theorem tailTrace_4400808 : CollatzResearch.WordTrace tailWord_4400808 prefixEnd_4400808 2259729772151723052161059 := by
  unfold tailWord_4400808
  simp only [CollatzResearch.WordTrace]
  refine ⟨80255327120315844506861539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107007102827087792675815385 80255327120315844506861539)
  ·
    refine ⟨120382990680473766760292309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80255327120315844506861539 120382990680473766760292309)
    ·
      refine ⟨2821476344073603908444351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 120382990680473766760292309 2821476344073603908444351)
      ·
        refine ⟨4232214516110405862666527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2821476344073603908444351 4232214516110405862666527)
        ·
          refine ⟨6348321774165608793999791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4232214516110405862666527 6348321774165608793999791)
          ·
            refine ⟨9522482661248413190999687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6348321774165608793999791 9522482661248413190999687)
            ·
              refine ⟨14283723991872619786499531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9522482661248413190999687 14283723991872619786499531)
              ·
                refine ⟨21425585987808929679749297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14283723991872619786499531 21425585987808929679749297)
                ·
                  refine ⟨16069189490856697259811973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21425585987808929679749297 16069189490856697259811973)
                  ·
                    refine ⟨3012973029535630736214745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16069189490856697259811973 3012973029535630736214745)
                    ·
                      refine ⟨2259729772151723052161059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3012973029535630736214745 2259729772151723052161059)
                      ·
                        rfl

theorem cell23_4400808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_4400808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4400808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4400808 prefixEnd_4400808 := by exact prefixLift 4400808
  have htrace : WordTrace (prefixWord ++ tailWord_4400808) baseStart_4400808 baseEnd_4400808 := by
    simpa [prefixWord, tailWord_4400808, baseEnd_4400808] using wordTrace_append hprefix tailTrace_4400808
  have hstable : (prefixWord ++ tailWord_4400808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4400808).length < 2 ^ (prefixWord ++ tailWord_4400808).sum := by decide
  have hdescent : baseEnd_4400808 < baseStart_4400808 := by decide
  rcases family_descends (prefixWord ++ tailWord_4400808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4400840 : List Nat := [2, 1, 3, 1, 2, 2, 1, 4, 1, 6]
def baseStart_4400840 : Nat := 118140960795 + 4400840 * 2 ^ 59
def prefixEnd_4400840 : Nat := 4983230072969 + 3 ^ 40 * 4400840 * 2
def baseEnd_4400840 : Nat := 753248734510888975653637

theorem tailTrace_4400840 : CollatzResearch.WordTrace tailWord_4400840 prefixEnd_4400840 753248734510888975653637 := by
  unfold tailWord_4400840
  simp only [CollatzResearch.WordTrace]
  refine ⟨80255910688257879239443987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107007880917677172319258649 80255910688257879239443987)
  ·
    refine ⟨120383866032386818859165981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80255910688257879239443987 120383866032386818859165981)
    ·
      refine ⟨45143949762145057072187243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120383866032386818859165981 45143949762145057072187243)
      ·
        refine ⟨67715924643217585608280865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45143949762145057072187243 67715924643217585608280865)
        ·
          refine ⟨50786943482413189206210649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67715924643217585608280865 50786943482413189206210649)
          ·
            refine ⟨38090207611809891904657987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50786943482413189206210649 38090207611809891904657987)
            ·
              refine ⟨57135311417714837856986981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38090207611809891904657987 57135311417714837856986981)
              ·
                refine ⟨10712870890821532098185059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57135311417714837856986981 10712870890821532098185059)
                ·
                  refine ⟨16069306336232298147277589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10712870890821532098185059 16069306336232298147277589)
                  ·
                    refine ⟨753248734510888975653637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16069306336232298147277589 753248734510888975653637)
                    ·
                      rfl

theorem cell23_4400840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 4, 1, 6].length) (baseStart_4400840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4400840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4400840 prefixEnd_4400840 := by exact prefixLift 4400840
  have htrace : WordTrace (prefixWord ++ tailWord_4400840) baseStart_4400840 baseEnd_4400840 := by
    simpa [prefixWord, tailWord_4400840, baseEnd_4400840] using wordTrace_append hprefix tailTrace_4400840
  have hstable : (prefixWord ++ tailWord_4400840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4400840).length < 2 ^ (prefixWord ++ tailWord_4400840).sum := by decide
  have hdescent : baseEnd_4400840 < baseStart_4400840 := by decide
  rcases family_descends (prefixWord ++ tailWord_4400840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4400844 : List Nat := [2, 2, 1, 5, 2, 1, 1, 3, 1, 5]
def baseStart_4400844 : Nat := 118140960795 + 4400844 * 2 ^ 59
def prefixEnd_4400844 : Nat := 4983230072969 + 3 ^ 40 * 4400844 * 2
def baseEnd_4400844 : Nat := 753249419151761637103631

theorem tailTrace_4400844 : CollatzResearch.WordTrace tailWord_4400844 prefixEnd_4400844 753249419151761637103631 := by
  unfold tailWord_4400844
  simp only [CollatzResearch.WordTrace]
  refine ⟨80255983634250633581016793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107007978179000844774689057 80255983634250633581016793)
  ·
    refine ⟨60191987725687975185762595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80255983634250633581016793 60191987725687975185762595)
    ·
      refine ⟨90287981588531962778643893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60191987725687975185762595 90287981588531962778643893)
      ·
        refine ⟨8464498273924871510497865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 90287981588531962778643893 8464498273924871510497865)
        ·
          refine ⟨6348373705443653632873399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8464498273924871510497865 6348373705443653632873399)
          ·
            refine ⟨9522560558165480449310099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6348373705443653632873399 9522560558165480449310099)
            ·
              refine ⟨14283840837248220673965149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9522560558165480449310099 14283840837248220673965149)
              ·
                refine ⟨5356440313968082752736931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14283840837248220673965149 5356440313968082752736931)
                ·
                  refine ⟨8034660470952124129105397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5356440313968082752736931 8034660470952124129105397)
                  ·
                    refine ⟨753249419151761637103631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8034660470952124129105397 753249419151761637103631)
                    ·
                      rfl

theorem cell23_4400844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 3, 1, 5].length) (baseStart_4400844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4400844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4400844 prefixEnd_4400844 := by exact prefixLift 4400844
  have htrace : WordTrace (prefixWord ++ tailWord_4400844) baseStart_4400844 baseEnd_4400844 := by
    simpa [prefixWord, tailWord_4400844, baseEnd_4400844] using wordTrace_append hprefix tailTrace_4400844
  have hstable : (prefixWord ++ tailWord_4400844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4400844).length < 2 ^ (prefixWord ++ tailWord_4400844).sum := by decide
  have hdescent : baseEnd_4400844 < baseStart_4400844 := by decide
  rcases family_descends (prefixWord ++ tailWord_4400844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4400857 : List Nat := [1, 2, 1, 2, 3, 4, 1, 1, 4, 4]
def baseStart_4400857 : Nat := 118140960795 + 4400857 * 2 ^ 59
def prefixEnd_4400857 : Nat := 4983230072969 + 3 ^ 40 * 4400857 * 2
def baseEnd_4400857 : Nat := 753251644234597786816111

theorem tailTrace_4400857 : CollatzResearch.WordTrace tailWord_4400857 prefixEnd_4400857 753251644234597786816111 := by
  unfold tailWord_4400857
  simp only [CollatzResearch.WordTrace]
  refine ⟨160512441417454170382256825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107008294278302780254837883 160512441417454170382256825)
  ·
    refine ⟨120384331063090627786692619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160512441417454170382256825 120384331063090627786692619)
    ·
      refine ⟨180576496594635941680038929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120384331063090627786692619 180576496594635941680038929)
      ·
        refine ⟨135432372445976956260029197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180576496594635941680038929 135432372445976956260029197)
        ·
          refine ⟨50787139667241358597510949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135432372445976956260029197 50787139667241358597510949)
          ·
            refine ⟨9522588687607754737033303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50787139667241358597510949 9522588687607754737033303)
            ·
              refine ⟨14283883031411632105549955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9522588687607754737033303 14283883031411632105549955)
              ·
                refine ⟨21425824547117448158324933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14283883031411632105549955 21425824547117448158324933)
                ·
                  refine ⟨4017342102584521529685925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21425824547117448158324933 4017342102584521529685925)
                  ·
                    refine ⟨753251644234597786816111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4017342102584521529685925 753251644234597786816111)
                    ·
                      rfl

theorem cell23_4400857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 4, 4].length) (baseStart_4400857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4400857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4400857 prefixEnd_4400857 := by exact prefixLift 4400857
  have htrace : WordTrace (prefixWord ++ tailWord_4400857) baseStart_4400857 baseEnd_4400857 := by
    simpa [prefixWord, tailWord_4400857, baseEnd_4400857] using wordTrace_append hprefix tailTrace_4400857
  have hstable : (prefixWord ++ tailWord_4400857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4400857).length < 2 ^ (prefixWord ++ tailWord_4400857).sum := by decide
  have hdescent : baseEnd_4400857 < baseStart_4400857 := by decide
  rcases family_descends (prefixWord ++ tailWord_4400857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4400864 : List Nat := [2, 1, 1, 3, 1, 2, 3, 3, 3, 2, 2]
def baseStart_4400864 : Nat := 118140960795 + 4400864 * 2 ^ 59
def prefixEnd_4400864 : Nat := 4983230072969 + 3 ^ 40 * 4400864 * 2
def baseEnd_4400864 : Nat := 2259758527068374833060801

theorem tailTrace_4400864 : CollatzResearch.WordTrace tailWord_4400864 prefixEnd_4400864 2259758527068374833060801 := by
  unfold tailWord_4400864
  simp only [CollatzResearch.WordTrace]
  refine ⟨80256348364214405288880823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107008464485619207051841097 80256348364214405288880823)
  ·
    refine ⟨120384522546321607933321235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80256348364214405288880823 120384522546321607933321235)
    ·
      refine ⟨180576783819482411899981853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120384522546321607933321235 180576783819482411899981853)
      ·
        refine ⟨67716293932305904462493195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 180576783819482411899981853 67716293932305904462493195)
        ·
          refine ⟨101574440898458856693739793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67716293932305904462493195 101574440898458856693739793)
          ·
            refine ⟨76180830673844142520304845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101574440898458856693739793 76180830673844142520304845)
            ·
              refine ⟨28567811502691553445114317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76180830673844142520304845 28567811502691553445114317)
              ·
                refine ⟨10712929313509332541917869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28567811502691553445114317 10712929313509332541917869)
                ·
                  refine ⟨4017348492565999703219201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10712929313509332541917869 4017348492565999703219201)
                  ·
                    refine ⟨3013011369424499777414401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4017348492565999703219201 3013011369424499777414401)
                    ·
                      refine ⟨2259758527068374833060801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3013011369424499777414401 2259758527068374833060801)
                      ·
                        rfl

theorem cell23_4400864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 3, 3, 2, 2].length) (baseStart_4400864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4400864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4400864 prefixEnd_4400864 := by exact prefixLift 4400864
  have htrace : WordTrace (prefixWord ++ tailWord_4400864) baseStart_4400864 baseEnd_4400864 := by
    simpa [prefixWord, tailWord_4400864, baseEnd_4400864] using wordTrace_append hprefix tailTrace_4400864
  have hstable : (prefixWord ++ tailWord_4400864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4400864).length < 2 ^ (prefixWord ++ tailWord_4400864).sum := by decide
  have hdescent : baseEnd_4400864 < baseStart_4400864 := by decide
  rcases family_descends (prefixWord ++ tailWord_4400864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4400877 : List Nat := [1, 5, 1, 2, 1, 3, 1, 1, 1, 1, 6]
def baseStart_4400877 : Nat := 118140960795 + 4400877 * 2 ^ 59
def prefixEnd_4400877 : Nat := 4983230072969 + 3 ^ 40 * 4400877 * 2
def baseEnd_4400877 : Nat := 2259765202316883282198241

theorem tailTrace_4400877 : CollatzResearch.WordTrace tailWord_4400877 prefixEnd_4400877 2259765202316883282198241 := by
  unfold tailWord_4400877
  simp only [CollatzResearch.WordTrace]
  refine ⟨160513170877381713797984885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107008780584921142531989923 160513170877381713797984885)
  ·
    refine ⟨15048109769754535668561083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 160513170877381713797984885 15048109769754535668561083)
    ·
      refine ⟨22572164654631803502841625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15048109769754535668561083 22572164654631803502841625)
      ·
        refine ⟨16929123490973852627131219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22572164654631803502841625 16929123490973852627131219)
        ·
          refine ⟨25393685236460778940696829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16929123490973852627131219 25393685236460778940696829)
          ·
            refine ⟨9522631963672792102761311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25393685236460778940696829 9522631963672792102761311)
            ·
              refine ⟨14283947945509188154141967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9522631963672792102761311 14283947945509188154141967)
              ·
                refine ⟨21425921918263782231212951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14283947945509188154141967 21425921918263782231212951)
                ·
                  refine ⟨32138882877395673346819427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21425921918263782231212951 32138882877395673346819427)
                  ·
                    refine ⟨48208324316093510020229141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32138882877395673346819427 48208324316093510020229141)
                    ·
                      refine ⟨2259765202316883282198241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48208324316093510020229141 2259765202316883282198241)
                      ·
                        rfl

theorem cell23_4400877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_4400877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4400877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4400877 prefixEnd_4400877 := by exact prefixLift 4400877
  have htrace : WordTrace (prefixWord ++ tailWord_4400877) baseStart_4400877 baseEnd_4400877 := by
    simpa [prefixWord, tailWord_4400877, baseEnd_4400877] using wordTrace_append hprefix tailTrace_4400877
  have hstable : (prefixWord ++ tailWord_4400877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4400877).length < 2 ^ (prefixWord ++ tailWord_4400877).sum := by decide
  have hdescent : baseEnd_4400877 < baseStart_4400877 := by decide
  rcases family_descends (prefixWord ++ tailWord_4400877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4400897 : List Nat := [1, 2, 4, 1, 1, 1, 2, 4, 1, 3, 3]
def baseStart_4400897 : Nat := 118140960795 + 4400897 * 2 ^ 59
def prefixEnd_4400897 : Nat := 4983230072969 + 3 ^ 40 * 4400897 * 2
def baseEnd_4400897 : Nat := 2259775471929973203948149

theorem tailTrace_4400897 : CollatzResearch.WordTrace tailWord_4400897 prefixEnd_4400897 2259775471929973203948149 := by
  unfold tailWord_4400897
  simp only [CollatzResearch.WordTrace]
  refine ⟨160513900337309257213712945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107009266891539504809141963 160513900337309257213712945)
  ·
    refine ⟨120385425252981942910284709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160513900337309257213712945 120385425252981942910284709)
    ·
      refine ⟨22572267234934114295678383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120385425252981942910284709 22572267234934114295678383)
      ·
        refine ⟨33858400852401171443517575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22572267234934114295678383 33858400852401171443517575)
        ·
          refine ⟨50787601278601757165276363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33858400852401171443517575 50787601278601757165276363)
          ·
            refine ⟨76181401917902635747914545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50787601278601757165276363 76181401917902635747914545)
            ·
              refine ⟨57136051438426976810935909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76181401917902635747914545 57136051438426976810935909)
              ·
                refine ⟨10713009644705058152050483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57136051438426976810935909 10713009644705058152050483)
                ·
                  refine ⟨16069514467057587228075725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10713009644705058152050483 16069514467057587228075725)
                  ·
                    refine ⟨6026067925146595210528397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16069514467057587228075725 6026067925146595210528397)
                    ·
                      refine ⟨2259775471929973203948149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6026067925146595210528397 2259775471929973203948149)
                      ·
                        rfl

theorem cell23_4400897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 4, 1, 3, 3].length) (baseStart_4400897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4400897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4400897 prefixEnd_4400897 := by exact prefixLift 4400897
  have htrace : WordTrace (prefixWord ++ tailWord_4400897) baseStart_4400897 baseEnd_4400897 := by
    simpa [prefixWord, tailWord_4400897, baseEnd_4400897] using wordTrace_append hprefix tailTrace_4400897
  have hstable : (prefixWord ++ tailWord_4400897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4400897).length < 2 ^ (prefixWord ++ tailWord_4400897).sum := by decide
  have hdescent : baseEnd_4400897 < baseStart_4400897 := by decide
  rcases family_descends (prefixWord ++ tailWord_4400897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4400909 : List Nat := [1, 7, 2, 1, 2, 1, 1, 1, 3, 1, 3]
def baseStart_4400909 : Nat := 118140960795 + 4400909 * 2 ^ 59
def prefixEnd_4400909 : Nat := 4983230072969 + 3 ^ 40 * 4400909 * 2
def baseEnd_4400909 : Nat := 2259781633697827156998095

theorem tailTrace_4400909 : CollatzResearch.WordTrace tailWord_4400909 prefixEnd_4400909 2259781633697827156998095 := by
  unfold tailWord_4400909
  simp only [CollatzResearch.WordTrace]
  refine ⟨160514338013265783263149781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107009558675510522175433187 160514338013265783263149781)
  ·
    refine ⟨3762054797185916795230073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 160514338013265783263149781 3762054797185916795230073)
    ·
      refine ⟨2821541097889437596422555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3762054797185916795230073 2821541097889437596422555)
      ·
        refine ⟨4232311646834156394633833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2821541097889437596422555 4232311646834156394633833)
        ·
          refine ⟨3174233735125617295975375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4232311646834156394633833 3174233735125617295975375)
          ·
            refine ⟨4761350602688425943963063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3174233735125617295975375 4761350602688425943963063)
            ·
              refine ⟨7142025904032638915944595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4761350602688425943963063 7142025904032638915944595)
              ·
                refine ⟨10713038856048958373916893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7142025904032638915944595 10713038856048958373916893)
                ·
                  refine ⟨4017389571018359390218835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10713038856048958373916893 4017389571018359390218835)
                  ·
                    refine ⟨6026084356527539085328253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4017389571018359390218835 6026084356527539085328253)
                    ·
                      refine ⟨2259781633697827156998095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6026084356527539085328253 2259781633697827156998095)
                      ·
                        rfl

theorem cell23_4400909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_4400909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4400909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4400909 prefixEnd_4400909 := by exact prefixLift 4400909
  have htrace : WordTrace (prefixWord ++ tailWord_4400909) baseStart_4400909 baseEnd_4400909 := by
    simpa [prefixWord, tailWord_4400909, baseEnd_4400909] using wordTrace_append hprefix tailTrace_4400909
  have hstable : (prefixWord ++ tailWord_4400909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4400909).length < 2 ^ (prefixWord ++ tailWord_4400909).sum := by decide
  have hdescent : baseEnd_4400909 < baseStart_4400909 := by decide
  rcases family_descends (prefixWord ++ tailWord_4400909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4400924 : List Nat := [2, 2, 3, 1, 1, 2, 2, 2, 3, 3, 2]
def baseStart_4400924 : Nat := 118140960795 + 4400924 * 2 ^ 59
def prefixEnd_4400924 : Nat := 4983230072969 + 3 ^ 40 * 4400924 * 2
def baseEnd_4400924 : Nat := 2259789335907644598310525

theorem tailTrace_4400924 : CollatzResearch.WordTrace tailWord_4400924 prefixEnd_4400924 2259789335907644598310525 := by
  unfold tailWord_4400924
  simp only [CollatzResearch.WordTrace]
  refine ⟨80257442554105720412472913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107009923405474293883297217 80257442554105720412472913)
  ·
    refine ⟨60193081915579290309354685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80257442554105720412472913 60193081915579290309354685)
    ·
      refine ⟨22572405718342233866008007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60193081915579290309354685 22572405718342233866008007)
      ·
        refine ⟨33858608577513350799012011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22572405718342233866008007 33858608577513350799012011)
        ·
          refine ⟨50787912866270026198518017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33858608577513350799012011 50787912866270026198518017)
          ·
            refine ⟨38090934649702519648888513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50787912866270026198518017 38090934649702519648888513)
            ·
              refine ⟨28568200987276889736666385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38090934649702519648888513 28568200987276889736666385)
              ·
                refine ⟨21426150740457667302499789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28568200987276889736666385 21426150740457667302499789)
                ·
                  refine ⟨8034806527671625238437421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21426150740457667302499789 8034806527671625238437421)
                  ·
                    refine ⟨3013052447876859464414033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8034806527671625238437421 3013052447876859464414033)
                    ·
                      refine ⟨2259789335907644598310525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3013052447876859464414033 2259789335907644598310525)
                      ·
                        rfl

theorem cell23_4400924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 3, 3, 2].length) (baseStart_4400924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4400924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4400924 prefixEnd_4400924 := by exact prefixLift 4400924
  have htrace : WordTrace (prefixWord ++ tailWord_4400924) baseStart_4400924 baseEnd_4400924 := by
    simpa [prefixWord, tailWord_4400924, baseEnd_4400924] using wordTrace_append hprefix tailTrace_4400924
  have hstable : (prefixWord ++ tailWord_4400924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4400924).length < 2 ^ (prefixWord ++ tailWord_4400924).sum := by decide
  have hdescent : baseEnd_4400924 < baseStart_4400924 := by decide
  rcases family_descends (prefixWord ++ tailWord_4400924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4400931 : List Nat := [1, 1, 1, 4, 2, 1, 6, 1, 2, 1, 3]
def baseStart_4400931 : Nat := 118140960795 + 4400931 * 2 ^ 59
def prefixEnd_4400931 : Nat := 4983230072969 + 3 ^ 40 * 4400931 * 2
def baseEnd_4400931 : Nat := 2259792930272226070922993

theorem tailTrace_4400931 : CollatzResearch.WordTrace tailWord_4400931 prefixEnd_4400931 2259792930272226070922993 := by
  unfold tailWord_4400931
  simp only [CollatzResearch.WordTrace]
  refine ⟨160515140419186081020450647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107010093612790720680300431 160515140419186081020450647)
  ·
    refine ⟨240772710628779121530675971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160515140419186081020450647 240772710628779121530675971)
    ·
      refine ⟨361159065943168682296013957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240772710628779121530675971 361159065943168682296013957)
      ·
        refine ⟨67717324864344127930502617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 361159065943168682296013957 67717324864344127930502617)
        ·
          refine ⟨50787993648258095947876963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67717324864344127930502617 50787993648258095947876963)
          ·
            refine ⟨76181990472387143921815445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50787993648258095947876963 76181990472387143921815445)
            ·
              refine ⟨3571030803393147371335099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 76181990472387143921815445 3571030803393147371335099)
              ·
                refine ⟨5356546205089721057002649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3571030803393147371335099 5356546205089721057002649)
                ·
                  refine ⟨4017409653817290792751987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5356546205089721057002649 4017409653817290792751987)
                  ·
                    refine ⟨6026114480725936189127981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4017409653817290792751987 6026114480725936189127981)
                    ·
                      refine ⟨2259792930272226070922993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6026114480725936189127981 2259792930272226070922993)
                      ·
                        rfl

theorem cell23_4400931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 6, 1, 2, 1, 3].length) (baseStart_4400931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4400931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4400931 prefixEnd_4400931 := by exact prefixLift 4400931
  have htrace : WordTrace (prefixWord ++ tailWord_4400931) baseStart_4400931 baseEnd_4400931 := by
    simpa [prefixWord, tailWord_4400931, baseEnd_4400931] using wordTrace_append hprefix tailTrace_4400931
  have hstable : (prefixWord ++ tailWord_4400931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4400931).length < 2 ^ (prefixWord ++ tailWord_4400931).sum := by decide
  have hdescent : baseEnd_4400931 < baseStart_4400931 := by decide
  rcases family_descends (prefixWord ++ tailWord_4400931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4400954 : List Nat := [3, 1, 1, 1, 5, 1, 1, 1, 3, 4, 2]
def baseStart_4400954 : Nat := 118140960795 + 4400954 * 2 ^ 59
def prefixEnd_4400954 : Nat := 4983230072969 + 3 ^ 40 * 4400954 * 2
def baseEnd_4400954 : Nat := 2259804740327279480935387

theorem tailTrace_4400954 : CollatzResearch.WordTrace tailWord_4400954 prefixEnd_4400954 2259804740327279480935387 := by
  unfold tailWord_4400954
  simp only [CollatzResearch.WordTrace]
  refine ⟨40128994824525688987134479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107010652865401837299025277 40128994824525688987134479)
  ·
    refine ⟨60193492236788533480701719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40128994824525688987134479 60193492236788533480701719)
    ·
      refine ⟨90290238355182800221052579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60193492236788533480701719 90290238355182800221052579)
      ·
        refine ⟨135435357532774200331578869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90290238355182800221052579 135435357532774200331578869)
        ·
          refine ⟨12697064768697581281085519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 135435357532774200331578869 12697064768697581281085519)
          ·
            refine ⟨19045597153046371921628279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12697064768697581281085519 19045597153046371921628279)
            ·
              refine ⟨28568395729569557882442419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19045597153046371921628279 28568395729569557882442419)
              ·
                refine ⟨42852593594354336823663629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28568395729569557882442419 42852593594354336823663629)
                ·
                  refine ⟨16069722597882876308873861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42852593594354336823663629 16069722597882876308873861)
                  ·
                    refine ⟨3013072987103039307913849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16069722597882876308873861 3013072987103039307913849)
                    ·
                      refine ⟨2259804740327279480935387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3013072987103039307913849 2259804740327279480935387)
                      ·
                        rfl

theorem cell23_4400954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 3, 4, 2].length) (baseStart_4400954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4400954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4400954 prefixEnd_4400954 := by exact prefixLift 4400954
  have htrace : WordTrace (prefixWord ++ tailWord_4400954) baseStart_4400954 baseEnd_4400954 := by
    simpa [prefixWord, tailWord_4400954, baseEnd_4400954] using wordTrace_append hprefix tailTrace_4400954
  have hstable : (prefixWord ++ tailWord_4400954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4400954).length < 2 ^ (prefixWord ++ tailWord_4400954).sum := by decide
  have hdescent : baseEnd_4400954 < baseStart_4400954 := by decide
  rcases family_descends (prefixWord ++ tailWord_4400954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4400988 : List Nat := [2, 2, 4, 2, 2, 1, 2, 1, 1, 4, 2]
def baseStart_4400988 : Nat := 118140960795 + 4400988 * 2 ^ 59
def prefixEnd_4400988 : Nat := 4983230072969 + 3 ^ 40 * 4400988 * 2
def baseEnd_4400988 : Nat := 2259822198669532347910231

theorem tailTrace_4400988 : CollatzResearch.WordTrace tailWord_4400988 prefixEnd_4400988 2259822198669532347910231 := by
  unfold tailWord_4400988
  simp only [CollatzResearch.WordTrace]
  refine ⟨80258609689989789877637809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107011479586653053170183745 80258609689989789877637809)
  ·
    refine ⟨60193957267492342408228357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80258609689989789877637809 60193957267492342408228357)
    ·
      refine ⟨11286366987654814201542817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60193957267492342408228357 11286366987654814201542817)
      ·
        refine ⟨8464775240741110651157113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11286366987654814201542817 8464775240741110651157113)
        ·
          refine ⟨6348581430555832988367835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8464775240741110651157113 6348581430555832988367835)
          ·
            refine ⟨9522872145833749482551753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6348581430555832988367835 9522872145833749482551753)
            ·
              refine ⟨7142154109375312111913815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9522872145833749482551753 7142154109375312111913815)
              ·
                refine ⟨10713231164062968167870723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7142154109375312111913815 10713231164062968167870723)
                ·
                  refine ⟨16069846746094452251806085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10713231164062968167870723 16069846746094452251806085)
                  ·
                    refine ⟨3013096264892709797213641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16069846746094452251806085 3013096264892709797213641)
                    ·
                      refine ⟨2259822198669532347910231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3013096264892709797213641 2259822198669532347910231)
                      ·
                        rfl

theorem cell23_4400988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_4400988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4400988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4400988 prefixEnd_4400988 := by exact prefixLift 4400988
  have htrace : WordTrace (prefixWord ++ tailWord_4400988) baseStart_4400988 baseEnd_4400988 := by
    simpa [prefixWord, tailWord_4400988, baseEnd_4400988] using wordTrace_append hprefix tailTrace_4400988
  have hstable : (prefixWord ++ tailWord_4400988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4400988).length < 2 ^ (prefixWord ++ tailWord_4400988).sum := by decide
  have hdescent : baseEnd_4400988 < baseStart_4400988 := by decide
  rcases family_descends (prefixWord ++ tailWord_4400988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4400994 : List Nat := [3, 3, 2, 1, 2, 2, 1, 2, 7]
def baseStart_4400994 : Nat := 118140960795 + 4400994 * 2 ^ 59
def prefixEnd_4400994 : Nat := 4983230072969 + 3 ^ 40 * 4400994 * 2
def baseEnd_4400994 : Nat := 251091697728162147159467

theorem tailTrace_4400994 : CollatzResearch.WordTrace tailWord_4400994 prefixEnd_4400994 251091697728162147159467 := by
  unfold tailWord_4400994
  simp only [CollatzResearch.WordTrace]
  refine ⟨40129359554489460694998509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107011625478638561853329357 40129359554489460694998509)
  ·
    refine ⟨15048509832933547760624441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40129359554489460694998509 15048509832933547760624441)
    ·
      refine ⟨11286382374700160820468331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15048509832933547760624441 11286382374700160820468331)
      ·
        refine ⟨16929573562050241230702497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11286382374700160820468331 16929573562050241230702497)
        ·
          refine ⟨12697180171537680923026873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16929573562050241230702497 12697180171537680923026873)
          ·
            refine ⟨9522885128653260692270155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12697180171537680923026873 9522885128653260692270155)
            ·
              refine ⟨14284327692979891038405233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9522885128653260692270155 14284327692979891038405233)
              ·
                refine ⟨10713245769734918278803925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14284327692979891038405233 10713245769734918278803925)
                ·
                  refine ⟨251091697728162147159467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10713245769734918278803925 251091697728162147159467)
                  ·
                    rfl

theorem cell23_4400994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 2, 7].length) (baseStart_4400994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4400994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4400994 prefixEnd_4400994 := by exact prefixLift 4400994
  have htrace : WordTrace (prefixWord ++ tailWord_4400994) baseStart_4400994 baseEnd_4400994 := by
    simpa [prefixWord, tailWord_4400994, baseEnd_4400994] using wordTrace_append hprefix tailTrace_4400994
  have hstable : (prefixWord ++ tailWord_4400994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4400994).length < 2 ^ (prefixWord ++ tailWord_4400994).sum := by decide
  have hdescent : baseEnd_4400994 < baseStart_4400994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4400994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4401022 : List Nat := [4, 2, 3, 1, 1, 3, 1, 2, 2, 2, 2]
def baseStart_4401022 : Nat := 118140960795 + 4401022 * 2 ^ 59
def prefixEnd_4401022 : Nat := 4983230072969 + 3 ^ 40 * 4401022 * 2
def baseEnd_4401022 : Nat := 2259839657011785214885075

theorem tailTrace_4401022 : CollatzResearch.WordTrace tailWord_4401022 prefixEnd_4401022 2259839657011785214885075 := by
  unfold tailWord_4401022
  simp only [CollatzResearch.WordTrace]
  refine ⟨20064807432732050445251665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107012306307904269041342213 20064807432732050445251665)
  ·
    refine ⟨15048605574549037833938749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20064807432732050445251665 15048605574549037833938749)
    ·
      refine ⟨5643227090455889187727031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15048605574549037833938749 5643227090455889187727031)
      ·
        refine ⟨8464840635683833781590547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5643227090455889187727031 8464840635683833781590547)
        ·
          refine ⟨12697260953525750672385821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8464840635683833781590547 12697260953525750672385821)
          ·
            refine ⟨4761472857572156502144683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12697260953525750672385821 4761472857572156502144683)
            ·
              refine ⟨7142209286358234753217025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4761472857572156502144683 7142209286358234753217025)
              ·
                refine ⟨5356656964768676064912769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7142209286358234753217025 5356656964768676064912769)
                ·
                  refine ⟨4017492723576507048684577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5356656964768676064912769 4017492723576507048684577)
                  ·
                    refine ⟨3013119542682380286513433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4017492723576507048684577 3013119542682380286513433)
                    ·
                      refine ⟨2259839657011785214885075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3013119542682380286513433 2259839657011785214885075)
                      ·
                        rfl

theorem cell23_4401022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_4401022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4401022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4401022 prefixEnd_4401022 := by exact prefixLift 4401022
  have htrace : WordTrace (prefixWord ++ tailWord_4401022) baseStart_4401022 baseEnd_4401022 := by
    simpa [prefixWord, tailWord_4401022, baseEnd_4401022] using wordTrace_append hprefix tailTrace_4401022
  have hstable : (prefixWord ++ tailWord_4401022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4401022).length < 2 ^ (prefixWord ++ tailWord_4401022).sum := by decide
  have hdescent : baseEnd_4401022 < baseStart_4401022 := by decide
  rcases family_descends (prefixWord ++ tailWord_4401022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4401044 : List Nat := [2, 4, 2, 1, 1, 2, 1, 2, 1, 3, 4]
def baseStart_4401044 : Nat := 118140960795 + 4401044 * 2 ^ 59
def prefixEnd_4401044 : Nat := 4983230072969 + 3 ^ 40 * 4401044 * 2
def baseEnd_4401044 : Nat := 2259850953586184128809973

theorem tailTrace_4401044 : CollatzResearch.WordTrace tailWord_4401044 prefixEnd_4401044 2259850953586184128809973 := by
  unfold tailWord_4401044
  simp only [CollatzResearch.WordTrace]
  refine ⟨80259630933888350659657093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107012841245184467546209457 80259630933888350659657093)
  ·
    refine ⟨15048680800104065748685705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80259630933888350659657093 15048680800104065748685705)
    ·
      refine ⟨11286510600078049311514279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15048680800104065748685705 11286510600078049311514279)
      ·
        refine ⟨16929765900117073967271419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11286510600078049311514279 16929765900117073967271419)
        ·
          refine ⟨25394648850175610950907129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16929765900117073967271419 25394648850175610950907129)
          ·
            refine ⟨19045986637631708213180347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25394648850175610950907129 19045986637631708213180347)
            ·
              refine ⟨28568979956447562319770521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19045986637631708213180347 28568979956447562319770521)
              ·
                refine ⟨21426734967335671739827891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28568979956447562319770521 21426734967335671739827891)
                ·
                  refine ⟨32140102451003507609741837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21426734967335671739827891 32140102451003507609741837)
                  ·
                    refine ⟨12052538419126315353653189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32140102451003507609741837 12052538419126315353653189)
                    ·
                      refine ⟨2259850953586184128809973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12052538419126315353653189 2259850953586184128809973)
                      ·
                        rfl

theorem cell23_4401044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_4401044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4401044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4401044 prefixEnd_4401044 := by exact prefixLift 4401044
  have htrace : WordTrace (prefixWord ++ tailWord_4401044) baseStart_4401044 baseEnd_4401044 := by
    simpa [prefixWord, tailWord_4401044, baseEnd_4401044] using wordTrace_append hprefix tailTrace_4401044
  have hstable : (prefixWord ++ tailWord_4401044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4401044).length < 2 ^ (prefixWord ++ tailWord_4401044).sum := by decide
  have hdescent : baseEnd_4401044 < baseStart_4401044 := by decide
  rcases family_descends (prefixWord ++ tailWord_4401044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4401088 : List Nat := [2, 1, 1, 2, 3, 2, 5, 2, 1, 4]
def baseStart_4401088 : Nat := 118140960795 + 4401088 * 2 ^ 59
def prefixEnd_4401088 : Nat := 4983230072969 + 3 ^ 40 * 4401088 * 2
def baseEnd_4401088 : Nat := 753291182244993985553257

theorem tailTrace_4401088 : CollatzResearch.WordTrace tailWord_4401088 prefixEnd_4401088 753291182244993985553257 := by
  unfold tailWord_4401088
  simp only [CollatzResearch.WordTrace]
  refine ⟨80260433339808648416957959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107013911119744864555943945 80260433339808648416957959)
  ·
    refine ⟨120390650009712972625436939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80260433339808648416957959 120390650009712972625436939)
    ·
      refine ⟨180585975014569458938155409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120390650009712972625436939 180585975014569458938155409)
      ·
        refine ⟨135439481260927094203616557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180585975014569458938155409 135439481260927094203616557)
        ·
          refine ⟨50789805472847660326356209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135439481260927094203616557 50789805472847660326356209)
          ·
            refine ⟨38092354104635745244767157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50789805472847660326356209 38092354104635745244767157)
            ·
              refine ⟨3571158197309601116696921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38092354104635745244767157 3571158197309601116696921)
              ·
                refine ⟨2678368647982200837522691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3571158197309601116696921 2678368647982200837522691)
                ·
                  refine ⟨4017552971973301256284037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2678368647982200837522691 4017552971973301256284037)
                  ·
                    refine ⟨753291182244993985553257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4017552971973301256284037 753291182244993985553257)
                    ·
                      rfl

theorem cell23_4401088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 5, 2, 1, 4].length) (baseStart_4401088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4401088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4401088 prefixEnd_4401088 := by exact prefixLift 4401088
  have htrace : WordTrace (prefixWord ++ tailWord_4401088) baseStart_4401088 baseEnd_4401088 := by
    simpa [prefixWord, tailWord_4401088, baseEnd_4401088] using wordTrace_append hprefix tailTrace_4401088
  have hstable : (prefixWord ++ tailWord_4401088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4401088).length < 2 ^ (prefixWord ++ tailWord_4401088).sum := by decide
  have hdescent : baseEnd_4401088 < baseStart_4401088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4401088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4401097 : List Nat := [1, 2, 1, 1, 2, 1, 2, 3, 5, 5]
def baseStart_4401097 : Nat := 118140960795 + 4401097 * 2 ^ 59
def prefixEnd_4401097 : Nat := 4983230072969 + 3 ^ 40 * 4401097 * 2
def baseEnd_4401097 : Nat := 753292722686957473815743

theorem tailTrace_4401097 : CollatzResearch.WordTrace tailWord_4401097 prefixEnd_4401097 753292722686957473815743 := by
  unfold tailWord_4401097
  simp only [CollatzResearch.WordTrace]
  refine ⟨160521194936584691370993545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107014129957723127580662363 160521194936584691370993545)
  ·
    refine ⟨120390896202438518528245159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160521194936584691370993545 120390896202438518528245159)
    ·
      refine ⟨180586344303657777792367739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120390896202438518528245159 180586344303657777792367739)
      ·
        refine ⟨270879516455486666688551609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180586344303657777792367739 270879516455486666688551609)
        ·
          refine ⟨203159637341615000016413707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 270879516455486666688551609 203159637341615000016413707)
          ·
            refine ⟨304739456012422500024620561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203159637341615000016413707 304739456012422500024620561)
            ·
              refine ⟨228554592009316875018465421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 304739456012422500024620561 228554592009316875018465421)
              ·
                refine ⟨85707972003493828131924533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 228554592009316875018465421 85707972003493828131924533)
                ·
                  refine ⟨8035122375327546387367925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 85707972003493828131924533 8035122375327546387367925)
                  ·
                    refine ⟨753292722686957473815743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8035122375327546387367925 753292722686957473815743)
                    ·
                      rfl

theorem cell23_4401097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 5, 5].length) (baseStart_4401097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4401097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4401097 prefixEnd_4401097 := by exact prefixLift 4401097
  have htrace : WordTrace (prefixWord ++ tailWord_4401097) baseStart_4401097 baseEnd_4401097 := by
    simpa [prefixWord, tailWord_4401097, baseEnd_4401097] using wordTrace_append hprefix tailTrace_4401097
  have hstable : (prefixWord ++ tailWord_4401097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4401097).length < 2 ^ (prefixWord ++ tailWord_4401097).sum := by decide
  have hdescent : baseEnd_4401097 < baseStart_4401097 := by decide
  rcases family_descends (prefixWord ++ tailWord_4401097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4401104 : List Nat := [2, 1, 1, 1, 1, 2, 4, 1, 3, 5, 2]
def baseStart_4401104 : Nat := 118140960795 + 4401104 * 2 ^ 59
def prefixEnd_4401104 : Nat := 4983230072969 + 3 ^ 40 * 4401104 * 2
def baseEnd_4401104 : Nat := 2259881762425453894059697

theorem tailTrace_4401104 : CollatzResearch.WordTrace tailWord_4401104 prefixEnd_4401104 2259881762425453894059697 := by
  unfold tailWord_4401104
  simp only [CollatzResearch.WordTrace]
  refine ⟨80260725123779665783249183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107014300165039554377665577 80260725123779665783249183)
  ·
    refine ⟨120391087685669498674873775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80260725123779665783249183 120391087685669498674873775)
    ·
      refine ⟨180586631528504248012310663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120391087685669498674873775 180586631528504248012310663)
      ·
        refine ⟨270879947292756372018465995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180586631528504248012310663 270879947292756372018465995)
        ·
          refine ⟨406319920939134558027698993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270879947292756372018465995 406319920939134558027698993)
          ·
            refine ⟨304739940704350918520774245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 406319920939134558027698993 304739940704350918520774245)
            ·
              refine ⟨57138738882065797222645171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 304739940704350918520774245 57138738882065797222645171)
              ·
                refine ⟨85708108323098695833967757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57138738882065797222645171 85708108323098695833967757)
                ·
                  refine ⟨32140540621162010937737909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 85708108323098695833967757 32140540621162010937737909)
                  ·
                    refine ⟨3013175683233938525412929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32140540621162010937737909 3013175683233938525412929)
                    ·
                      refine ⟨2259881762425453894059697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3013175683233938525412929 2259881762425453894059697)
                      ·
                        rfl

theorem cell23_4401104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 3, 5, 2].length) (baseStart_4401104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4401104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4401104 prefixEnd_4401104 := by exact prefixLift 4401104
  have htrace : WordTrace (prefixWord ++ tailWord_4401104) baseStart_4401104 baseEnd_4401104 := by
    simpa [prefixWord, tailWord_4401104, baseEnd_4401104] using wordTrace_append hprefix tailTrace_4401104
  have hstable : (prefixWord ++ tailWord_4401104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4401104).length < 2 ^ (prefixWord ++ tailWord_4401104).sum := by decide
  have hdescent : baseEnd_4401104 < baseStart_4401104 := by decide
  rcases family_descends (prefixWord ++ tailWord_4401104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4401121 : List Nat := [1, 2, 3, 1, 2, 1, 3, 3, 2, 3, 2]
def baseStart_4401121 : Nat := 118140960795 + 4401121 * 2 ^ 59
def prefixEnd_4401121 : Nat := 4983230072969 + 3 ^ 40 * 4401121 * 2
def baseEnd_4401121 : Nat := 2259890491596580327547119

theorem tailTrace_4401121 : CollatzResearch.WordTrace tailWord_4401121 prefixEnd_4401121 2259890491596580327547119 := by
  unfold tailWord_4401121
  simp only [CollatzResearch.WordTrace]
  refine ⟨160522070288497743469867217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107014713525665162313244811 160522070288497743469867217)
  ·
    refine ⟨120391552716373307602400413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160522070288497743469867217 120391552716373307602400413)
    ·
      refine ⟨45146832268639990350900155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120391552716373307602400413 45146832268639990350900155)
      ·
        refine ⟨67720248402959985526350233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45146832268639990350900155 67720248402959985526350233)
        ·
          refine ⟨50790186302219989144762675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67720248402959985526350233 50790186302219989144762675)
          ·
            refine ⟨76185279453329983717144013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50790186302219989144762675 76185279453329983717144013)
            ·
              refine ⟨28569479794998743893929005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76185279453329983717144013 28569479794998743893929005)
              ·
                refine ⟨10713554923124528960223377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28569479794998743893929005 10713554923124528960223377)
                ·
                  refine ⟨8035166192343396720167533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10713554923124528960223377 8035166192343396720167533)
                  ·
                    refine ⟨3013187322128773770062825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8035166192343396720167533 3013187322128773770062825)
                    ·
                      refine ⟨2259890491596580327547119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3013187322128773770062825 2259890491596580327547119)
                      ·
                        rfl

theorem cell23_4401121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 3, 2, 3, 2].length) (baseStart_4401121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4401121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4401121 prefixEnd_4401121 := by exact prefixLift 4401121
  have htrace : WordTrace (prefixWord ++ tailWord_4401121) baseStart_4401121 baseEnd_4401121 := by
    simpa [prefixWord, tailWord_4401121, baseEnd_4401121] using wordTrace_append hprefix tailTrace_4401121
  have hstable : (prefixWord ++ tailWord_4401121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4401121).length < 2 ^ (prefixWord ++ tailWord_4401121).sum := by decide
  have hdescent : baseEnd_4401121 < baseStart_4401121 := by decide
  rcases family_descends (prefixWord ++ tailWord_4401121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4401128 : List Nat := [2, 1, 4, 1, 1, 1, 1, 7, 1, 1, 3]
def baseStart_4401128 : Nat := 118140960795 + 4401128 * 2 ^ 59
def prefixEnd_4401128 : Nat := 4983230072969 + 3 ^ 40 * 4401128 * 2
def baseEnd_4401128 : Nat := 2259894085961161800159587

theorem tailTrace_4401128 : CollatzResearch.WordTrace tailWord_4401128 prefixEnd_4401128 2259894085961161800159587 := by
  unfold tailWord_4401128
  simp only [CollatzResearch.WordTrace]
  refine ⟨80261162799736191832686019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107014883732981589110248025 80261162799736191832686019)
  ·
    refine ⟨120391744199604287749029029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80261162799736191832686019 120391744199604287749029029)
    ·
      refine ⟨22573452037425803952942943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120391744199604287749029029 22573452037425803952942943)
      ·
        refine ⟨33860178056138705929414415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22573452037425803952942943 33860178056138705929414415)
        ·
          refine ⟨50790267084208058894121623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33860178056138705929414415 50790267084208058894121623)
          ·
            refine ⟨76185400626312088341182435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50790267084208058894121623 76185400626312088341182435)
            ·
              refine ⟨114278100939468132511773653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76185400626312088341182435 114278100939468132511773653)
              ·
                refine ⟨2678392990768784355744695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 114278100939468132511773653 2678392990768784355744695)
                ·
                  refine ⟨4017589486153176533617043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2678392990768784355744695 4017589486153176533617043)
                  ·
                    refine ⟨6026384229229764800425565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4017589486153176533617043 6026384229229764800425565)
                    ·
                      refine ⟨2259894085961161800159587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6026384229229764800425565 2259894085961161800159587)
                      ·
                        rfl

theorem cell23_4401128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 7, 1, 1, 3].length) (baseStart_4401128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4401128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4401128 prefixEnd_4401128 := by exact prefixLift 4401128
  have htrace : WordTrace (prefixWord ++ tailWord_4401128) baseStart_4401128 baseEnd_4401128 := by
    simpa [prefixWord, tailWord_4401128, baseEnd_4401128] using wordTrace_append hprefix tailTrace_4401128
  have hstable : (prefixWord ++ tailWord_4401128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4401128).length < 2 ^ (prefixWord ++ tailWord_4401128).sum := by decide
  have hdescent : baseEnd_4401128 < baseStart_4401128 := by decide
  rcases family_descends (prefixWord ++ tailWord_4401128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4401144 : List Nat := [2, 1, 2, 1, 1, 3, 2, 3, 4, 4]
def baseStart_4401144 : Nat := 118140960795 + 4401144 * 2 ^ 59
def prefixEnd_4401144 : Nat := 4983230072969 + 3 ^ 40 * 4401144 * 2
def baseEnd_4401144 : Nat := 753300767217211245853171

theorem tailTrace_4401144 : CollatzResearch.WordTrace tailWord_4401144 prefixEnd_4401144 753300767217211245853171 := by
  unfold tailWord_4401144
  simp only [CollatzResearch.WordTrace]
  refine ⟨80261454583707209198977243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107015272778276278931969657 80261454583707209198977243)
  ·
    refine ⟨120392181875560813798465865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80261454583707209198977243 120392181875560813798465865)
    ·
      refine ⟨90294136406670610348849399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120392181875560813798465865 90294136406670610348849399)
      ·
        refine ⟨135441204610005915523274099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90294136406670610348849399 135441204610005915523274099)
        ·
          refine ⟨203161806915008873284911149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135441204610005915523274099 203161806915008873284911149)
          ·
            refine ⟨76185677593128327481841681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 203161806915008873284911149 76185677593128327481841681)
            ·
              refine ⟨57139258194846245611381261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76185677593128327481841681 57139258194846245611381261)
              ·
                refine ⟨21427221823067342104267973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57139258194846245611381261 21427221823067342104267973)
                ·
                  refine ⟨4017604091825126644550245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21427221823067342104267973 4017604091825126644550245)
                  ·
                    refine ⟨753300767217211245853171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4017604091825126644550245 753300767217211245853171)
                    ·
                      rfl

theorem cell23_4401144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 4, 4].length) (baseStart_4401144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4401144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4401144 prefixEnd_4401144 := by exact prefixLift 4401144
  have htrace : WordTrace (prefixWord ++ tailWord_4401144) baseStart_4401144 baseEnd_4401144 := by
    simpa [prefixWord, tailWord_4401144, baseEnd_4401144] using wordTrace_append hprefix tailTrace_4401144
  have hstable : (prefixWord ++ tailWord_4401144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4401144).length < 2 ^ (prefixWord ++ tailWord_4401144).sum := by decide
  have hdescent : baseEnd_4401144 < baseStart_4401144 := by decide
  rcases family_descends (prefixWord ++ tailWord_4401144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4401145 : List Nat := [1, 2, 1, 3, 1, 4, 4, 2, 1, 1, 3]
def baseStart_4401145 : Nat := 118140960795 + 4401145 * 2 ^ 59
def prefixEnd_4401145 : Nat := 4983230072969 + 3 ^ 40 * 4401145 * 2
def baseEnd_4401145 : Nat := 2259902815132288233647009

theorem tailTrace_4401145 : CollatzResearch.WordTrace tailWord_4401145 prefixEnd_4401145 2259902815132288233647009 := by
  unfold tailWord_4401145
  simp only [CollatzResearch.WordTrace]
  refine ⟨160522945640410795568740889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107015297093607197045827259 160522945640410795568740889)
  ·
    refine ⟨120392209230308096676555667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160522945640410795568740889 120392209230308096676555667)
    ·
      refine ⟨180588313845462145014833501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120392209230308096676555667 180588313845462145014833501)
      ·
        refine ⟨67720617692048304380562563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 180588313845462145014833501 67720617692048304380562563)
        ·
          refine ⟨101580926538072456570843845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67720617692048304380562563 101580926538072456570843845)
          ·
            refine ⟨19046423725888585607033221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 101580926538072456570843845 19046423725888585607033221)
            ·
              refine ⟨3571204448604109801318729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19046423725888585607033221 3571204448604109801318729)
              ·
                refine ⟨2678403336453082350989047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3571204448604109801318729 2678403336453082350989047)
                ·
                  refine ⟨4017605004679623526483571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2678403336453082350989047 4017605004679623526483571)
                  ·
                    refine ⟨6026407507019435289725357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4017605004679623526483571 6026407507019435289725357)
                    ·
                      refine ⟨2259902815132288233647009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6026407507019435289725357 2259902815132288233647009)
                      ·
                        rfl

theorem cell23_4401145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 4, 2, 1, 1, 3].length) (baseStart_4401145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4401145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4401145 prefixEnd_4401145 := by exact prefixLift 4401145
  have htrace : WordTrace (prefixWord ++ tailWord_4401145) baseStart_4401145 baseEnd_4401145 := by
    simpa [prefixWord, tailWord_4401145, baseEnd_4401145] using wordTrace_append hprefix tailTrace_4401145
  have hstable : (prefixWord ++ tailWord_4401145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4401145).length < 2 ^ (prefixWord ++ tailWord_4401145).sum := by decide
  have hdescent : baseEnd_4401145 < baseStart_4401145 := by decide
  rcases family_descends (prefixWord ++ tailWord_4401145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4401147 : List Nat := [1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 6]
def baseStart_4401147 : Nat := 118140960795 + 4401147 * 2 ^ 59
def prefixEnd_4401147 : Nat := 4983230072969 + 3 ^ 40 * 4401147 * 2
def baseEnd_4401147 : Nat := 2259903842093597225821999

theorem tailTrace_4401147 : CollatzResearch.WordTrace tailWord_4401147 prefixEnd_4401147 2259903842093597225821999 := by
  unfold tailWord_4401147
  simp only [CollatzResearch.WordTrace]
  refine ⟨160523018586403549910313695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107015345724269033273542463 160523018586403549910313695)
  ·
    refine ⟨240784527879605324865470543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160523018586403549910313695 240784527879605324865470543)
    ·
      refine ⟨361176791819407987298205815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240784527879605324865470543 361176791819407987298205815)
      ·
        refine ⟨541765187729111980947308723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 361176791819407987298205815 541765187729111980947308723)
        ·
          refine ⟨812647781593667971420963085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 541765187729111980947308723 812647781593667971420963085)
          ·
            refine ⟨304742918097625489282861157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 812647781593667971420963085 304742918097625489282861157)
            ·
              refine ⟨57139297143304779240536467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 304742918097625489282861157 57139297143304779240536467)
              ·
                refine ⟨85708945714957168860804701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57139297143304779240536467 85708945714957168860804701)
                ·
                  refine ⟨32140854643108938322801763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 85708945714957168860804701 32140854643108938322801763)
                  ·
                    refine ⟨48211281964663407484202645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32140854643108938322801763 48211281964663407484202645)
                    ·
                      refine ⟨2259903842093597225821999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48211281964663407484202645 2259903842093597225821999)
                      ·
                        rfl

theorem cell23_4401147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 6].length) (baseStart_4401147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4401147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4401147 prefixEnd_4401147 := by exact prefixLift 4401147
  have htrace : WordTrace (prefixWord ++ tailWord_4401147) baseStart_4401147 baseEnd_4401147 := by
    simpa [prefixWord, tailWord_4401147, baseEnd_4401147] using wordTrace_append hprefix tailTrace_4401147
  have hstable : (prefixWord ++ tailWord_4401147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4401147).length < 2 ^ (prefixWord ++ tailWord_4401147).sum := by decide
  have hdescent : baseEnd_4401147 < baseStart_4401147 := by decide
  rcases family_descends (prefixWord ++ tailWord_4401147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4401151 : List Nat := [1, 1, 2, 2, 1, 2, 1, 2, 7, 2, 2]
def baseStart_4401151 : Nat := 118140960795 + 4401151 * 2 ^ 59
def prefixEnd_4401151 : Nat := 4983230072969 + 3 ^ 40 * 4401151 * 2
def baseEnd_4401151 : Nat := 2259905896016215210171981

theorem tailTrace_4401151 : CollatzResearch.WordTrace tailWord_4401151 prefixEnd_4401151 2259905896016215210171981 := by
  unfold tailWord_4401151
  simp only [CollatzResearch.WordTrace]
  refine ⟨160523164478389058593459307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107015442985592705728972871 160523164478389058593459307)
  ·
    refine ⟨240784746717583587890188961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160523164478389058593459307 240784746717583587890188961)
    ·
      refine ⟨180588560038187690917641721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 240784746717583587890188961 180588560038187690917641721)
      ·
        refine ⟨135441420028640768188231291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180588560038187690917641721 135441420028640768188231291)
        ·
          refine ⟨203162130042961152282346937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135441420028640768188231291 203162130042961152282346937)
          ·
            refine ⟨152371597532220864211760203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 203162130042961152282346937 152371597532220864211760203)
            ·
              refine ⟨228557396298331296317640305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152371597532220864211760203 228557396298331296317640305)
              ·
                refine ⟨171418047223748472238230229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 228557396298331296317640305 171418047223748472238230229)
                ·
                  refine ⟨4017610481806604818083521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 171418047223748472238230229 4017610481806604818083521)
                  ·
                    refine ⟨3013207861354953613562641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4017610481806604818083521 3013207861354953613562641)
                    ·
                      refine ⟨2259905896016215210171981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3013207861354953613562641 2259905896016215210171981)
                      ·
                        rfl

theorem cell23_4401151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 7, 2, 2].length) (baseStart_4401151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4401151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4401151 prefixEnd_4401151 := by exact prefixLift 4401151
  have htrace : WordTrace (prefixWord ++ tailWord_4401151) baseStart_4401151 baseEnd_4401151 := by
    simpa [prefixWord, tailWord_4401151, baseEnd_4401151] using wordTrace_append hprefix tailTrace_4401151
  have hstable : (prefixWord ++ tailWord_4401151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4401151).length < 2 ^ (prefixWord ++ tailWord_4401151).sum := by decide
  have hdescent : baseEnd_4401151 < baseStart_4401151 := by decide
  rcases family_descends (prefixWord ++ tailWord_4401151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4401181 : List Nat := [1, 4, 2, 2, 2, 1, 2, 2, 1, 2, 4]
def baseStart_4401181 : Nat := 118140960795 + 4401181 * 2 ^ 59
def prefixEnd_4401181 : Nat := 4983230072969 + 3 ^ 40 * 4401181 * 2
def baseEnd_4401181 : Nat := 2259921300435850092796843

theorem tailTrace_4401181 : CollatzResearch.WordTrace tailWord_4401181 prefixEnd_4401181 2259921300435850092796843 := by
  unfold tailWord_4401181
  simp only [CollatzResearch.WordTrace]
  refine ⟨160524258668280373717051397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107016172445520249144700931 160524258668280373717051397)
  ·
    refine ⟨30098298500302570071947137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 160524258668280373717051397 30098298500302570071947137)
    ·
      refine ⟨22573723875226927553960353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30098298500302570071947137 22573723875226927553960353)
      ·
        refine ⟨16930292906420195665470265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22573723875226927553960353 16930292906420195665470265)
        ·
          refine ⟨12697719679815146749102699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16930292906420195665470265 12697719679815146749102699)
          ·
            refine ⟨19046579519722720123654049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12697719679815146749102699 19046579519722720123654049)
            ·
              refine ⟨14284934639792040092740537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19046579519722720123654049 14284934639792040092740537)
              ·
                refine ⟨10713700979844030069555403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14284934639792040092740537 10713700979844030069555403)
                ·
                  refine ⟨16070551469766045104333105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10713700979844030069555403 16070551469766045104333105)
                  ·
                    refine ⟨12052913602324533828249829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16070551469766045104333105 12052913602324533828249829)
                    ·
                      refine ⟨2259921300435850092796843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12052913602324533828249829 2259921300435850092796843)
                      ·
                        rfl

theorem cell23_4401181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_4401181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4401181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4401181 prefixEnd_4401181 := by exact prefixLift 4401181
  have htrace : WordTrace (prefixWord ++ tailWord_4401181) baseStart_4401181 baseEnd_4401181 := by
    simpa [prefixWord, tailWord_4401181, baseEnd_4401181] using wordTrace_append hprefix tailTrace_4401181
  have hstable : (prefixWord ++ tailWord_4401181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4401181).length < 2 ^ (prefixWord ++ tailWord_4401181).sum := by decide
  have hdescent : baseEnd_4401181 < baseStart_4401181 := by decide
  rcases family_descends (prefixWord ++ tailWord_4401181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4401185 : List Nat := [1, 2, 3, 2, 4, 2, 2, 1, 1, 1, 4]
def baseStart_4401185 : Nat := 118140960795 + 4401185 * 2 ^ 59
def prefixEnd_4401185 : Nat := 4983230072969 + 3 ^ 40 * 4401185 * 2
def baseEnd_4401185 : Nat := 2259923354358468077146825

theorem tailTrace_4401185 : CollatzResearch.WordTrace tailWord_4401185 prefixEnd_4401185 2259923354358468077146825 := by
  unfold tailWord_4401185
  simp only [CollatzResearch.WordTrace]
  refine ⟨160524404560265882400197009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107016269706843921600131339 160524404560265882400197009)
  ·
    refine ⟨120393303420199411800147757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160524404560265882400197009 120393303420199411800147757)
    ·
      refine ⟨45147488782574779425055409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120393303420199411800147757 45147488782574779425055409)
      ·
        refine ⟨33860616586931084568791557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45147488782574779425055409 33860616586931084568791557)
        ·
          refine ⟨6348865610049578356648417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33860616586931084568791557 6348865610049578356648417)
          ·
            refine ⟨4761649207537183767486313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6348865610049578356648417 4761649207537183767486313)
            ·
              refine ⟨3571236905652887825614735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4761649207537183767486313 3571236905652887825614735)
              ·
                refine ⟨5356855358479331738422103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3571236905652887825614735 5356855358479331738422103)
                ·
                  refine ⟨8035283037718997607633155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5356855358479331738422103 8035283037718997607633155)
                  ·
                    refine ⟨12052924556578496411449733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8035283037718997607633155 12052924556578496411449733)
                    ·
                      refine ⟨2259923354358468077146825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12052924556578496411449733 2259923354358468077146825)
                      ·
                        rfl

theorem cell23_4401185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 2, 1, 1, 1, 4].length) (baseStart_4401185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4401185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4401185 prefixEnd_4401185 := by exact prefixLift 4401185
  have htrace : WordTrace (prefixWord ++ tailWord_4401185) baseStart_4401185 baseEnd_4401185 := by
    simpa [prefixWord, tailWord_4401185, baseEnd_4401185] using wordTrace_append hprefix tailTrace_4401185
  have hstable : (prefixWord ++ tailWord_4401185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4401185).length < 2 ^ (prefixWord ++ tailWord_4401185).sum := by decide
  have hdescent : baseEnd_4401185 < baseStart_4401185 := by decide
  rcases family_descends (prefixWord ++ tailWord_4401185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4401191 : List Nat := [1, 1, 7, 1, 2, 1, 10]
def baseStart_4401191 : Nat := 118140960795 + 4401191 * 2 ^ 59
def prefixEnd_4401191 : Nat := 4983230072969 + 3 ^ 40 * 4401191 * 2
def baseEnd_4401191 : Nat := 27900326361017222884837

theorem tailTrace_4401191 : CollatzResearch.WordTrace tailWord_4401191 prefixEnd_4401191 27900326361017222884837 := by
  unfold tailWord_4401191
  simp only [CollatzResearch.WordTrace]
  refine ⟨160524623398244145424915427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107016415598829430283276951 160524623398244145424915427)
  ·
    refine ⟨240786935097366218137373141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160524623398244145424915427 240786935097366218137373141)
    ·
      refine ⟨5643443791344520737594683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 240786935097366218137373141 5643443791344520737594683)
      ·
        refine ⟨8465165687016781106392025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5643443791344520737594683 8465165687016781106392025)
        ·
          refine ⟨6348874265262585829794019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8465165687016781106392025 6348874265262585829794019)
          ·
            refine ⟨9523311397893878744691029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6348874265262585829794019 9523311397893878744691029)
            ·
              refine ⟨27900326361017222884837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9523311397893878744691029 27900326361017222884837)
              ·
                rfl

theorem cell23_4401191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 10].length) (baseStart_4401191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4401191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4401191 prefixEnd_4401191 := by exact prefixLift 4401191
  have htrace : WordTrace (prefixWord ++ tailWord_4401191) baseStart_4401191 baseEnd_4401191 := by
    simpa [prefixWord, tailWord_4401191, baseEnd_4401191] using wordTrace_append hprefix tailTrace_4401191
  have hstable : (prefixWord ++ tailWord_4401191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4401191).length < 2 ^ (prefixWord ++ tailWord_4401191).sum := by decide
  have hdescent : baseEnd_4401191 < baseStart_4401191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4401191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4401228 : List Nat := [2, 2, 1, 3, 1, 1, 3, 4, 1, 3, 2]
def baseStart_4401228 : Nat := 118140960795 + 4401228 * 2 ^ 59
def prefixEnd_4401228 : Nat := 4983230072969 + 3 ^ 40 * 4401228 * 2
def baseEnd_4401228 : Nat := 2259945434026611408909127

theorem tailTrace_4401228 : CollatzResearch.WordTrace tailWord_4401228 prefixEnd_4401228 2259945434026611408909127 := by
  unfold tailWord_4401228
  simp only [CollatzResearch.WordTrace]
  refine ⟨80262986449555050372006169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107017315266073400496008225 80262986449555050372006169)
  ·
    refine ⟨60197239837166287779004627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80262986449555050372006169 60197239837166287779004627)
    ·
      refine ⟨90295859755749431668506941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60197239837166287779004627 90295859755749431668506941)
      ·
        refine ⟨33860947408406036875690103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90295859755749431668506941 33860947408406036875690103)
        ·
          refine ⟨50791421112609055313535155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33860947408406036875690103 50791421112609055313535155)
          ·
            refine ⟨76187131668913582970302733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50791421112609055313535155 76187131668913582970302733)
            ·
              refine ⟨28570174375842593613863525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76187131668913582970302733 28570174375842593613863525)
              ·
                refine ⟨5356907695470486302599411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28570174375842593613863525 5356907695470486302599411)
                ·
                  refine ⟨8035361543205729453899117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5356907695470486302599411 8035361543205729453899117)
                  ·
                    refine ⟨3013260578702148545212169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8035361543205729453899117 3013260578702148545212169)
                    ·
                      refine ⟨2259945434026611408909127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3013260578702148545212169 2259945434026611408909127)
                      ·
                        rfl

theorem cell23_4401228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 4, 1, 3, 2].length) (baseStart_4401228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4401228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4401228 prefixEnd_4401228 := by exact prefixLift 4401228
  have htrace : WordTrace (prefixWord ++ tailWord_4401228) baseStart_4401228 baseEnd_4401228 := by
    simpa [prefixWord, tailWord_4401228, baseEnd_4401228] using wordTrace_append hprefix tailTrace_4401228
  have hstable : (prefixWord ++ tailWord_4401228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4401228).length < 2 ^ (prefixWord ++ tailWord_4401228).sum := by decide
  have hdescent : baseEnd_4401228 < baseStart_4401228 := by decide
  rcases family_descends (prefixWord ++ tailWord_4401228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4401241 : List Nat := [1, 2, 1, 2, 2, 1, 4, 1, 3, 4, 2]
def baseStart_4401241 : Nat := 118140960795 + 4401241 * 2 ^ 59
def prefixEnd_4401241 : Nat := 4983230072969 + 3 ^ 40 * 4401241 * 2
def baseEnd_4401241 : Nat := 2259952109275119858046567

theorem tailTrace_4401241 : CollatzResearch.WordTrace tailWord_4401241 prefixEnd_4401241 2259952109275119858046567 := by
  unfold tailWord_4401241
  simp only [CollatzResearch.WordTrace]
  refine ⟨160526447048063003964235577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107017631365375335976157051 160526447048063003964235577)
  ·
    refine ⟨120394835286047252973176683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160526447048063003964235577 120394835286047252973176683)
    ·
      refine ⟨180592252929070879459765025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120394835286047252973176683 180592252929070879459765025)
      ·
        refine ⟨135444189696803159594823769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180592252929070879459765025 135444189696803159594823769)
        ·
          refine ⟨101583142272602369696117827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135444189696803159594823769 101583142272602369696117827)
          ·
            refine ⟨152374713408903554544176741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101583142272602369696117827 152374713408903554544176741)
            ·
              refine ⟨28570258764169416477033139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 152374713408903554544176741 28570258764169416477033139)
              ·
                refine ⟨42855388146254124715549709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28570258764169416477033139 42855388146254124715549709)
                ·
                  refine ⟨16070770554845296768331141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42855388146254124715549709 16070770554845296768331141)
                  ·
                    refine ⟨3013269479033493144062089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16070770554845296768331141 3013269479033493144062089)
                    ·
                      refine ⟨2259952109275119858046567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3013269479033493144062089 2259952109275119858046567)
                      ·
                        rfl

theorem cell23_4401241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 3, 4, 2].length) (baseStart_4401241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4401241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4401241 prefixEnd_4401241 := by exact prefixLift 4401241
  have htrace : WordTrace (prefixWord ++ tailWord_4401241) baseStart_4401241 baseEnd_4401241 := by
    simpa [prefixWord, tailWord_4401241, baseEnd_4401241] using wordTrace_append hprefix tailTrace_4401241
  have hstable : (prefixWord ++ tailWord_4401241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4401241).length < 2 ^ (prefixWord ++ tailWord_4401241).sum := by decide
  have hdescent : baseEnd_4401241 < baseStart_4401241 := by decide
  rcases family_descends (prefixWord ++ tailWord_4401241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4401261 : List Nat := [1, 5, 1, 1, 2, 1, 2, 1, 2, 4, 3]
def baseStart_4401261 : Nat := 118140960795 + 4401261 * 2 ^ 59
def prefixEnd_4401261 : Nat := 4983230072969 + 3 ^ 40 * 4401261 * 2
def baseEnd_4401261 : Nat := 2259962378888209779796475

theorem tailTrace_4401261 : CollatzResearch.WordTrace tailWord_4401261 prefixEnd_4401261 2259962378888209779796475 := by
  unfold tailWord_4401261
  simp only [CollatzResearch.WordTrace]
  refine ⟨160527176507990547379963637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107018117671993698253309091 160527176507990547379963637)
  ·
    refine ⟨15049422797624113816871591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 160527176507990547379963637 15049422797624113816871591)
    ·
      refine ⟨22574134196436170725307387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15049422797624113816871591 22574134196436170725307387)
      ·
        refine ⟨33861201294654256087961081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22574134196436170725307387 33861201294654256087961081)
        ·
          refine ⟨25395900970990692065970811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33861201294654256087961081 25395900970990692065970811)
          ·
            refine ⟨38093851456486038098956217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25395900970990692065970811 38093851456486038098956217)
            ·
              refine ⟨28570388592364528574217163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38093851456486038098956217 28570388592364528574217163)
              ·
                refine ⟨42855582888546792861325745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28570388592364528574217163 42855582888546792861325745)
                ·
                  refine ⟨32141687166410094645994309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42855582888546792861325745 32141687166410094645994309)
                  ·
                    refine ⟨6026566343701892746123933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32141687166410094645994309 6026566343701892746123933)
                    ·
                      refine ⟨2259962378888209779796475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6026566343701892746123933 2259962378888209779796475)
                      ·
                        rfl

theorem cell23_4401261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 4, 3].length) (baseStart_4401261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4401261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4401261 prefixEnd_4401261 := by exact prefixLift 4401261
  have htrace : WordTrace (prefixWord ++ tailWord_4401261) baseStart_4401261 baseEnd_4401261 := by
    simpa [prefixWord, tailWord_4401261, baseEnd_4401261] using wordTrace_append hprefix tailTrace_4401261
  have hstable : (prefixWord ++ tailWord_4401261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4401261).length < 2 ^ (prefixWord ++ tailWord_4401261).sum := by decide
  have hdescent : baseEnd_4401261 < baseStart_4401261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4401261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4401298 : List Nat := [3, 2, 3, 1, 1, 1, 2, 5, 5]
def baseStart_4401298 : Nat := 118140960795 + 4401298 * 2 ^ 59
def prefixEnd_4401298 : Nat := 4983230072969 + 3 ^ 40 * 4401298 * 2
def baseEnd_4401298 : Nat := 251109041963602903892645

theorem tailTrace_4401298 : CollatzResearch.WordTrace tailWord_4401298 prefixEnd_4401298 251109041963602903892645 := by
  unfold tailWord_4401298
  simp only [CollatzResearch.WordTrace]
  refine ⟨40132131502214125674765137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107019017339237668466040365 40132131502214125674765137)
  ·
    refine ⟨30099098626660594256073853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40132131502214125674765137 30099098626660594256073853)
    ·
      refine ⟨11287161984997722846027695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30099098626660594256073853 11287161984997722846027695)
      ·
        refine ⟨16930742977496584269041543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11287161984997722846027695 16930742977496584269041543)
        ·
          refine ⟨25396114466244876403562315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16930742977496584269041543 25396114466244876403562315)
          ·
            refine ⟨38094171699367314605343473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25396114466244876403562315 38094171699367314605343473)
            ·
              refine ⟨28570628774525485954007605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38094171699367314605343473 28570628774525485954007605)
              ·
                refine ⟨2678496447611764308188213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28570628774525485954007605 2678496447611764308188213)
                ·
                  refine ⟨251109041963602903892645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2678496447611764308188213 251109041963602903892645)
                  ·
                    rfl

theorem cell23_4401298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 5, 5].length) (baseStart_4401298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4401298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4401298 prefixEnd_4401298 := by exact prefixLift 4401298
  have htrace : WordTrace (prefixWord ++ tailWord_4401298) baseStart_4401298 baseEnd_4401298 := by
    simpa [prefixWord, tailWord_4401298, baseEnd_4401298] using wordTrace_append hprefix tailTrace_4401298
  have hstable : (prefixWord ++ tailWord_4401298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4401298).length < 2 ^ (prefixWord ++ tailWord_4401298).sum := by decide
  have hdescent : baseEnd_4401298 < baseStart_4401298 := by decide
  rcases family_descends (prefixWord ++ tailWord_4401298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4401332 : List Nat := [2, 5, 3, 1, 1, 1, 1, 2, 7]
def baseStart_4401332 : Nat := 118140960795 + 4401332 * 2 ^ 59
def prefixEnd_4401332 : Nat := 4983230072969 + 3 ^ 40 * 4401332 * 2
def baseEnd_4401332 : Nat := 251110981779408778000961

theorem tailTrace_4401332 : CollatzResearch.WordTrace tailWord_4401332 prefixEnd_4401332 251110981779408778000961 := by
  unfold tailWord_4401332
  simp only [CollatzResearch.WordTrace]
  refine ⟨80264883045366663252899125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107019844060488884337198833 80264883045366663252899125)
  ·
    refine ⟨7524832785503124679959293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 80264883045366663252899125 7524832785503124679959293)
    ·
      refine ⟨2821812294563671754984735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7524832785503124679959293 2821812294563671754984735)
      ·
        refine ⟨4232718441845507632477103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2821812294563671754984735 4232718441845507632477103)
        ·
          refine ⟨6349077662768261448715655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4232718441845507632477103 6349077662768261448715655)
          ·
            refine ⟨9523616494152392173073483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6349077662768261448715655 9523616494152392173073483)
            ·
              refine ⟨14285424741228588259610225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9523616494152392173073483 14285424741228588259610225)
              ·
                refine ⟨10714068555921441194707669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14285424741228588259610225 10714068555921441194707669)
                ·
                  refine ⟨251110981779408778000961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10714068555921441194707669 251110981779408778000961)
                  ·
                    rfl

theorem cell23_4401332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_4401332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4401332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4401332 prefixEnd_4401332 := by exact prefixLift 4401332
  have htrace : WordTrace (prefixWord ++ tailWord_4401332) baseStart_4401332 baseEnd_4401332 := by
    simpa [prefixWord, tailWord_4401332, baseEnd_4401332] using wordTrace_append hprefix tailTrace_4401332
  have hstable : (prefixWord ++ tailWord_4401332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4401332).length < 2 ^ (prefixWord ++ tailWord_4401332).sum := by decide
  have hdescent : baseEnd_4401332 < baseStart_4401332 := by decide
  rcases family_descends (prefixWord ++ tailWord_4401332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4401348 : List Nat := [2, 3, 3, 1, 2, 2, 1, 1, 1, 3, 4]
def baseStart_4401348 : Nat := 118140960795 + 4401348 * 2 ^ 59
def prefixEnd_4401348 : Nat := 4983230072969 + 3 ^ 40 * 4401348 * 2
def baseEnd_4401348 : Nat := 2260007051705150939408575

theorem tailTrace_4401348 : CollatzResearch.WordTrace tailWord_4401348 prefixEnd_4401348 2260007051705150939408575 := by
  unfold tailWord_4401348
  simp only [CollatzResearch.WordTrace]
  refine ⟨80265174829337680619190349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107020233105783574158920465 80265174829337680619190349)
  ·
    refine ⟨30099440561001630232196381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80265174829337680619190349 30099440561001630232196381)
    ·
      refine ⟨11287290210375611337073643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30099440561001630232196381 11287290210375611337073643)
      ·
        refine ⟨16930935315563417005610465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11287290210375611337073643 16930935315563417005610465)
        ·
          refine ⟨12698201486672562754207849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16930935315563417005610465 12698201486672562754207849)
          ·
            refine ⟨9523651115004422065655887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12698201486672562754207849 9523651115004422065655887)
            ·
              refine ⟨14285476672506633098483831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9523651115004422065655887 14285476672506633098483831)
              ·
                refine ⟨21428215008759949647725747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14285476672506633098483831 21428215008759949647725747)
                ·
                  refine ⟨32142322513139924471588621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21428215008759949647725747 32142322513139924471588621)
                  ·
                    refine ⟨12053370942427471676845733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32142322513139924471588621 12053370942427471676845733)
                    ·
                      refine ⟨2260007051705150939408575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12053370942427471676845733 2260007051705150939408575)
                      ·
                        rfl

theorem cell23_4401348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_4401348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4401348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4401348 prefixEnd_4401348 := by exact prefixLift 4401348
  have htrace : WordTrace (prefixWord ++ tailWord_4401348) baseStart_4401348 baseEnd_4401348 := by
    simpa [prefixWord, tailWord_4401348, baseEnd_4401348] using wordTrace_append hprefix tailTrace_4401348
  have hstable : (prefixWord ++ tailWord_4401348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4401348).length < 2 ^ (prefixWord ++ tailWord_4401348).sum := by decide
  have hdescent : baseEnd_4401348 < baseStart_4401348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4401348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4401388 : List Nat := [2, 2, 1, 1, 2, 3, 5, 1, 6]
def baseStart_4401388 : Nat := 118140960795 + 4401388 * 2 ^ 59
def prefixEnd_4401388 : Nat := 4983230072969 + 3 ^ 40 * 4401388 * 2
def baseEnd_4401388 : Nat := 251114176770147864767599

theorem tailTrace_4401388 : CollatzResearch.WordTrace tailWord_4401388 prefixEnd_4401388 251114176770147864767599 := by
  unfold tailWord_4401388
  simp only [CollatzResearch.WordTrace]
  refine ⟨80265904289265224034918409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107021205719020298713224545 80265904289265224034918409)
  ·
    refine ⟨60199428216948918026188807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80265904289265224034918409 60199428216948918026188807)
    ·
      refine ⟨90299142325423377039283211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60199428216948918026188807 90299142325423377039283211)
      ·
        refine ⟨135448713488135065558924817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90299142325423377039283211 135448713488135065558924817)
        ·
          refine ⟨101586535116101299169193613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135448713488135065558924817 101586535116101299169193613)
          ·
            refine ⟨38094950668537987188447605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101586535116101299169193613 38094950668537987188447605)
            ·
              refine ⟨3571401625175436298916963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38094950668537987188447605 3571401625175436298916963)
              ·
                refine ⟨5357102437763154448375445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3571401625175436298916963 5357102437763154448375445)
                ·
                  refine ⟨251114176770147864767599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5357102437763154448375445 251114176770147864767599)
                  ·
                    rfl

theorem cell23_4401388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 6].length) (baseStart_4401388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4401388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4401388 prefixEnd_4401388 := by exact prefixLift 4401388
  have htrace : WordTrace (prefixWord ++ tailWord_4401388) baseStart_4401388 baseEnd_4401388 := by
    simpa [prefixWord, tailWord_4401388, baseEnd_4401388] using wordTrace_append hprefix tailTrace_4401388
  have hstable : (prefixWord ++ tailWord_4401388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4401388).length < 2 ^ (prefixWord ++ tailWord_4401388).sum := by decide
  have hdescent : baseEnd_4401388 < baseStart_4401388 := by decide
  rcases family_descends (prefixWord ++ tailWord_4401388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4401408 : List Nat := [2, 1, 1, 2, 1, 1, 6, 1, 1, 5, 2]
def baseStart_4401408 : Nat := 118140960795 + 4401408 * 2 ^ 59
def prefixEnd_4401408 : Nat := 4983230072969 + 3 ^ 40 * 4401408 * 2
def baseEnd_4401408 : Nat := 2260037860544420704658299

theorem tailTrace_4401408 : CollatzResearch.WordTrace tailWord_4401408 prefixEnd_4401408 2260037860544420704658299 := by
  unfold tailWord_4401408
  simp only [CollatzResearch.WordTrace]
  refine ⟨80266269019228995742782439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107021692025638660990376585 80266269019228995742782439)
  ·
    refine ⟨120399403528843493614173659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80266269019228995742782439 120399403528843493614173659)
    ·
      refine ⟨180599105293265240421260489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120399403528843493614173659 180599105293265240421260489)
      ·
        refine ⟨135449328969948930315945367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180599105293265240421260489 135449328969948930315945367)
        ·
          refine ⟨203173993454923395473918051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135449328969948930315945367 203173993454923395473918051)
          ·
            refine ⟨304760990182385093210877077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203173993454923395473918051 304760990182385093210877077)
            ·
              refine ⟨14285671414799301244259863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 304760990182385093210877077 14285671414799301244259863)
              ·
                refine ⟨21428507122198951866389795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14285671414799301244259863 21428507122198951866389795)
                ·
                  refine ⟨32142760683298427799584693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21428507122198951866389795 32142760683298427799584693)
                  ·
                    refine ⟨3013383814059227606211065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32142760683298427799584693 3013383814059227606211065)
                    ·
                      refine ⟨2260037860544420704658299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3013383814059227606211065 2260037860544420704658299)
                      ·
                        rfl

theorem cell23_4401408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 1, 5, 2].length) (baseStart_4401408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4401408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4401408 prefixEnd_4401408 := by exact prefixLift 4401408
  have htrace : WordTrace (prefixWord ++ tailWord_4401408) baseStart_4401408 baseEnd_4401408 := by
    simpa [prefixWord, tailWord_4401408, baseEnd_4401408] using wordTrace_append hprefix tailTrace_4401408
  have hstable : (prefixWord ++ tailWord_4401408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4401408).length < 2 ^ (prefixWord ++ tailWord_4401408).sum := by decide
  have hdescent : baseEnd_4401408 < baseStart_4401408 := by decide
  rcases family_descends (prefixWord ++ tailWord_4401408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4401418 : List Nat := [3, 1, 2, 2, 1, 1, 4, 3, 1, 5]
def baseStart_4401418 : Nat := 118140960795 + 4401418 * 2 ^ 59
def prefixEnd_4401418 : Nat := 4983230072969 + 3 ^ 40 * 4401418 * 2
def baseEnd_4401418 : Nat := 753347665116988555177751

theorem tailTrace_4401418 : CollatzResearch.WordTrace tailWord_4401418 prefixEnd_4401418 753347665116988555177751 := by
  unfold tailWord_4401418
  simp only [CollatzResearch.WordTrace]
  refine ⟨40133225692105440798357227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107021935178947842128952605 40133225692105440798357227)
  ·
    refine ⟨60199838538158161197535841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40133225692105440798357227 60199838538158161197535841)
    ·
      refine ⟨45149878903618620898151881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60199838538158161197535841 45149878903618620898151881)
      ·
        refine ⟨33862409177713965673613911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45149878903618620898151881 33862409177713965673613911)
        ·
          refine ⟨50793613766570948510420867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33862409177713965673613911 50793613766570948510420867)
          ·
            refine ⟨76190420649856422765631301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50793613766570948510420867 76190420649856422765631301)
            ·
              refine ⟨14285703871848079268555869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76190420649856422765631301 14285703871848079268555869)
              ·
                refine ⟨5357138951943029725708451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14285703871848079268555869 5357138951943029725708451)
                ·
                  refine ⟨8035708427914544588562677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5357138951943029725708451 8035708427914544588562677)
                  ·
                    refine ⟨753347665116988555177751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8035708427914544588562677 753347665116988555177751)
                    ·
                      rfl

theorem cell23_4401418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 3, 1, 5].length) (baseStart_4401418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4401418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4401418 prefixEnd_4401418 := by exact prefixLift 4401418
  have htrace : WordTrace (prefixWord ++ tailWord_4401418) baseStart_4401418 baseEnd_4401418 := by
    simpa [prefixWord, tailWord_4401418, baseEnd_4401418] using wordTrace_append hprefix tailTrace_4401418
  have hstable : (prefixWord ++ tailWord_4401418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4401418).length < 2 ^ (prefixWord ++ tailWord_4401418).sum := by decide
  have hdescent : baseEnd_4401418 < baseStart_4401418 := by decide
  rcases family_descends (prefixWord ++ tailWord_4401418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4401425 : List Nat := [1, 2, 2, 1, 1, 6, 1, 2, 2, 3, 2]
def baseStart_4401425 : Nat := 118140960795 + 4401425 * 2 ^ 59
def prefixEnd_4401425 : Nat := 4983230072969 + 3 ^ 40 * 4401425 * 2
def baseEnd_4401425 : Nat := 2260046589715547138145721

theorem tailTrace_4401425 : CollatzResearch.WordTrace tailWord_4401425 prefixEnd_4401425 2260046589715547138145721 := by
  unfold tailWord_4401425
  simp only [CollatzResearch.WordTrace]
  refine ⟨160533158079396403388933729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107022105386264268925955819 160533158079396403388933729)
  ·
    refine ⟨120399868559547302541700297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160533158079396403388933729 120399868559547302541700297)
    ·
      refine ⟨90299901419660476906275223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120399868559547302541700297 90299901419660476906275223)
      ·
        refine ⟨135449852129490715359412835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90299901419660476906275223 135449852129490715359412835)
        ·
          refine ⟨203174778194236073039119253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135449852129490715359412835 203174778194236073039119253)
          ·
            refine ⟨9523817727854815923708715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 203174778194236073039119253 9523817727854815923708715)
            ·
              refine ⟨14285726591782223885563073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9523817727854815923708715 14285726591782223885563073)
              ·
                refine ⟨10714294943836667914172305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14285726591782223885563073 10714294943836667914172305)
                ·
                  refine ⟨8035721207877500935629229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10714294943836667914172305 8035721207877500935629229)
                  ·
                    refine ⟨3013395452954062850860961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8035721207877500935629229 3013395452954062850860961)
                    ·
                      refine ⟨2260046589715547138145721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3013395452954062850860961 2260046589715547138145721)
                      ·
                        rfl

theorem cell23_4401425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 3, 2].length) (baseStart_4401425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4401425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4401425 prefixEnd_4401425 := by exact prefixLift 4401425
  have htrace : WordTrace (prefixWord ++ tailWord_4401425) baseStart_4401425 baseEnd_4401425 := by
    simpa [prefixWord, tailWord_4401425, baseEnd_4401425] using wordTrace_append hprefix tailTrace_4401425
  have hstable : (prefixWord ++ tailWord_4401425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4401425).length < 2 ^ (prefixWord ++ tailWord_4401425).sum := by decide
  have hdescent : baseEnd_4401425 < baseStart_4401425 := by decide
  rcases family_descends (prefixWord ++ tailWord_4401425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4401455 : List Nat := [1, 1, 2, 1, 2, 1, 4, 4, 3, 2, 2]
def baseStart_4401455 : Nat := 118140960795 + 4401455 * 2 ^ 59
def prefixEnd_4401455 : Nat := 4983230072969 + 3 ^ 40 * 4401455 * 2
def baseEnd_4401455 : Nat := 2260061994135182020770583

theorem tailTrace_4401455 : CollatzResearch.WordTrace tailWord_4401455 prefixEnd_4401455 2260061994135182020770583 := by
  unfold tailWord_4401455
  simp only [CollatzResearch.WordTrace]
  refine ⟨160534252269287718512525819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107022834846191812341683879 160534252269287718512525819)
  ·
    refine ⟨240801378403931577768788729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160534252269287718512525819 240801378403931577768788729)
    ·
      refine ⟨180601033802948683326591547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 240801378403931577768788729 180601033802948683326591547)
      ·
        refine ⟨270901550704423024989887321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180601033802948683326591547 270901550704423024989887321)
        ·
          refine ⟨203176163028317268742415491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 270901550704423024989887321 203176163028317268742415491)
          ·
            refine ⟨304764244542475903113623237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203176163028317268742415491 304764244542475903113623237)
            ·
              refine ⟨57143295851714231833804357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 304764244542475903113623237 57143295851714231833804357)
              ·
                refine ⟨10714367972196418468838317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57143295851714231833804357 10714367972196418468838317)
                ·
                  refine ⟨4017887989573656925814369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10714367972196418468838317 4017887989573656925814369)
                  ·
                    refine ⟨3013415992180242694360777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4017887989573656925814369 3013415992180242694360777)
                    ·
                      refine ⟨2260061994135182020770583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3013415992180242694360777 2260061994135182020770583)
                      ·
                        rfl

theorem cell23_4401455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 4, 3, 2, 2].length) (baseStart_4401455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4401455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4401455 prefixEnd_4401455 := by exact prefixLift 4401455
  have htrace : WordTrace (prefixWord ++ tailWord_4401455) baseStart_4401455 baseEnd_4401455 := by
    simpa [prefixWord, tailWord_4401455, baseEnd_4401455] using wordTrace_append hprefix tailTrace_4401455
  have hstable : (prefixWord ++ tailWord_4401455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4401455).length < 2 ^ (prefixWord ++ tailWord_4401455).sum := by decide
  have hdescent : baseEnd_4401455 < baseStart_4401455 := by decide
  rcases family_descends (prefixWord ++ tailWord_4401455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4401461 : List Nat := [1, 3, 3, 1, 2, 1, 1, 11]
def baseStart_4401461 : Nat := 118140960795 + 4401461 * 2 ^ 59
def prefixEnd_4401461 : Nat := 4983230072969 + 3 ^ 40 * 4401461 * 2
def baseEnd_4401461 : Nat := 83706113889596629529465

theorem tailTrace_4401461 : CollatzResearch.WordTrace tailWord_4401461 prefixEnd_4401461 83706113889596629529465 := by
  unfold tailWord_4401461
  simp only [CollatzResearch.WordTrace]
  refine ⟨160534471107265981537244237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107022980738177321024829491 160534471107265981537244237)
  ·
    refine ⟨60200426665224743076466589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160534471107265981537244237 60200426665224743076466589)
    ·
      refine ⟨22575159999459278653674971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60200426665224743076466589 22575159999459278653674971)
      ·
        refine ⟨33862739999188917980512457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22575159999459278653674971 33862739999188917980512457)
        ·
          refine ⟨25397054999391688485384343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33862739999188917980512457 25397054999391688485384343)
          ·
            refine ⟨38095582499087532728076515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25397054999391688485384343 38095582499087532728076515)
            ·
              refine ⟨57143373748631299092114773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38095582499087532728076515 57143373748631299092114773)
              ·
                refine ⟨83706113889596629529465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 57143373748631299092114773 83706113889596629529465)
                ·
                  rfl

theorem cell23_4401461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 11].length) (baseStart_4401461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4401461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4401461 prefixEnd_4401461 := by exact prefixLift 4401461
  have htrace : WordTrace (prefixWord ++ tailWord_4401461) baseStart_4401461 baseEnd_4401461 := by
    simpa [prefixWord, tailWord_4401461, baseEnd_4401461] using wordTrace_append hprefix tailTrace_4401461
  have hstable : (prefixWord ++ tailWord_4401461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4401461).length < 2 ^ (prefixWord ++ tailWord_4401461).sum := by decide
  have hdescent : baseEnd_4401461 < baseStart_4401461 := by decide
  rcases family_descends (prefixWord ++ tailWord_4401461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4401468 : List Nat := [2, 2, 2, 2, 1, 2, 3, 2, 1, 2, 4]
def baseStart_4401468 : Nat := 118140960795 + 4401468 * 2 ^ 59
def prefixEnd_4401468 : Nat := 4983230072969 + 3 ^ 40 * 4401468 * 2
def baseEnd_4401468 : Nat := 2260068669383690469908023

theorem tailTrace_4401468 : CollatzResearch.WordTrace tailWord_4401468 prefixEnd_4401468 2260068669383690469908023 := by
  unfold tailWord_4401468
  simp only [CollatzResearch.WordTrace]
  refine ⟨80267363209120310866374529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107023150945493747821832705 80267363209120310866374529)
  ·
    refine ⟨60200522406840233149780897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80267363209120310866374529 60200522406840233149780897)
    ·
      refine ⟨45150391805130174862335673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60200522406840233149780897 45150391805130174862335673)
      ·
        refine ⟨33862793853847631146751755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45150391805130174862335673 33862793853847631146751755)
        ·
          refine ⟨50794190780771446720127633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33862793853847631146751755 50794190780771446720127633)
          ·
            refine ⟨38095643085578585040095725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50794190780771446720127633 38095643085578585040095725)
            ·
              refine ⟨14285866157091969390035897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38095643085578585040095725 14285866157091969390035897)
              ·
                refine ⟨10714399617818977042526923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14285866157091969390035897 10714399617818977042526923)
                ·
                  refine ⟨16071599426728465563790385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10714399617818977042526923 16071599426728465563790385)
                  ·
                    refine ⟨12053699570046349172842789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16071599426728465563790385 12053699570046349172842789)
                    ·
                      refine ⟨2260068669383690469908023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12053699570046349172842789 2260068669383690469908023)
                      ·
                        rfl

theorem cell23_4401468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_4401468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4401468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4401468 prefixEnd_4401468 := by exact prefixLift 4401468
  have htrace : WordTrace (prefixWord ++ tailWord_4401468) baseStart_4401468 baseEnd_4401468 := by
    simpa [prefixWord, tailWord_4401468, baseEnd_4401468] using wordTrace_append hprefix tailTrace_4401468
  have hstable : (prefixWord ++ tailWord_4401468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4401468).length < 2 ^ (prefixWord ++ tailWord_4401468).sum := by decide
  have hdescent : baseEnd_4401468 < baseStart_4401468 := by decide
  rcases family_descends (prefixWord ++ tailWord_4401468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4401478 : List Nat := [6, 1, 1, 15]
def baseStart_4401478 : Nat := 118140960795 + 4401478 * 2 ^ 59
def prefixEnd_4401478 : Nat := 4983230072969 + 3 ^ 40 * 4401478 * 2
def baseEnd_4401478 : Nat := 1033412804842357307171

theorem tailTrace_4401478 : CollatzResearch.WordTrace tailWord_4401478 prefixEnd_4401478 1033412804842357307171 := by
  unfold tailWord_4401478
  simp only [CollatzResearch.WordTrace]
  refine ⟨5016721598381387295019159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 107023394098802928960408725 5016721598381387295019159)
  ·
    refine ⟨7525082397572080942528739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5016721598381387295019159 7525082397572080942528739)
    ·
      refine ⟨11287623596358121413793109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7525082397572080942528739 11287623596358121413793109)
      ·
        refine ⟨1033412804842357307171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 15 11287623596358121413793109 1033412804842357307171)
        ·
          rfl

theorem cell23_4401478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 15].length) (baseStart_4401478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4401478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4401478 prefixEnd_4401478 := by exact prefixLift 4401478
  have htrace : WordTrace (prefixWord ++ tailWord_4401478) baseStart_4401478 baseEnd_4401478 := by
    simpa [prefixWord, tailWord_4401478, baseEnd_4401478] using wordTrace_append hprefix tailTrace_4401478
  have hstable : (prefixWord ++ tailWord_4401478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4401478).length < 2 ^ (prefixWord ++ tailWord_4401478).sum := by decide
  have hdescent : baseEnd_4401478 < baseStart_4401478 := by decide
  rcases family_descends (prefixWord ++ tailWord_4401478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4401489 : List Nat := [1, 2, 2, 1, 4, 3, 1, 4, 1, 2, 2]
def baseStart_4401489 : Nat := 118140960795 + 4401489 * 2 ^ 59
def prefixEnd_4401489 : Nat := 4983230072969 + 3 ^ 40 * 4401489 * 2
def baseEnd_4401489 : Nat := 2260079452477434887745427

theorem tailTrace_4401489 : CollatzResearch.WordTrace tailWord_4401489 prefixEnd_4401489 2260079452477434887745427 := by
  unfold tailWord_4401489
  simp only [CollatzResearch.WordTrace]
  refine ⟨160535492351164542319263521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107023661567443028212842347 160535492351164542319263521)
  ·
    refine ⟨120401619263373406739447641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160535492351164542319263521 120401619263373406739447641)
    ·
      refine ⟨90301214447530055054585731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120401619263373406739447641 90301214447530055054585731)
      ·
        refine ⟨135451821671295082581878597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90301214447530055054585731 135451821671295082581878597)
        ·
          refine ⟨25397216563367827984102237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 135451821671295082581878597 25397216563367827984102237)
          ·
            refine ⟨9523956211262935494038339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25397216563367827984102237 9523956211262935494038339)
            ·
              refine ⟨14285934316894403241057509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9523956211262935494038339 14285934316894403241057509)
              ·
                refine ⟨2678612684417700607698283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14285934316894403241057509 2678612684417700607698283)
                ·
                  refine ⟨4017919026626550911547425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2678612684417700607698283 4017919026626550911547425)
                  ·
                    refine ⟨3013439269969913183660569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4017919026626550911547425 3013439269969913183660569)
                    ·
                      refine ⟨2260079452477434887745427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3013439269969913183660569 2260079452477434887745427)
                      ·
                        rfl

theorem cell23_4401489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 4, 1, 2, 2].length) (baseStart_4401489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4401489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4401489 prefixEnd_4401489 := by exact prefixLift 4401489
  have htrace : WordTrace (prefixWord ++ tailWord_4401489) baseStart_4401489 baseEnd_4401489 := by
    simpa [prefixWord, tailWord_4401489, baseEnd_4401489] using wordTrace_append hprefix tailTrace_4401489
  have hstable : (prefixWord ++ tailWord_4401489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4401489).length < 2 ^ (prefixWord ++ tailWord_4401489).sum := by decide
  have hdescent : baseEnd_4401489 < baseStart_4401489 := by decide
  rcases family_descends (prefixWord ++ tailWord_4401489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4401521 : List Nat := [1, 2, 2, 2, 1, 2, 1, 1, 3, 8]
def baseStart_4401521 : Nat := 118140960795 + 4401521 * 2 ^ 59
def prefixEnd_4401521 : Nat := 4983230072969 + 3 ^ 40 * 4401521 * 2
def baseEnd_4401521 : Nat := 753365294619459587515093

theorem tailTrace_4401521 : CollatzResearch.WordTrace tailWord_4401521 prefixEnd_4401521 753365294619459587515093 := by
  unfold tailWord_4401521
  simp only [CollatzResearch.WordTrace]
  refine ⟨160536659487048611784428417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107024439658032407856285611 160536659487048611784428417)
  ·
    refine ⟨120402494615286458838321313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160536659487048611784428417 120402494615286458838321313)
    ·
      refine ⟨90301870961464844128740985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120402494615286458838321313 90301870961464844128740985)
      ·
        refine ⟨67726403221098633096555739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90301870961464844128740985 67726403221098633096555739)
        ·
          refine ⟨101589604831647949644833609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67726403221098633096555739 101589604831647949644833609)
          ·
            refine ⟨76192203623735962233625207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101589604831647949644833609 76192203623735962233625207)
            ·
              refine ⟨114288305435603943350437811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76192203623735962233625207 114288305435603943350437811)
              ·
                refine ⟨171432458153405915025656717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114288305435603943350437811 171432458153405915025656717)
                ·
                  refine ⟨64287171807527218134621269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 171432458153405915025656717 64287171807527218134621269)
                  ·
                    refine ⟨753365294619459587515093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 64287171807527218134621269 753365294619459587515093)
                    ·
                      rfl

theorem cell23_4401521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 8].length) (baseStart_4401521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4401521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4401521 prefixEnd_4401521 := by exact prefixLift 4401521
  have htrace : WordTrace (prefixWord ++ tailWord_4401521) baseStart_4401521 baseEnd_4401521 := by
    simpa [prefixWord, tailWord_4401521, baseEnd_4401521] using wordTrace_append hprefix tailTrace_4401521
  have hstable : (prefixWord ++ tailWord_4401521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4401521).length < 2 ^ (prefixWord ++ tailWord_4401521).sum := by decide
  have hdescent : baseEnd_4401521 < baseStart_4401521 := by decide
  rcases family_descends (prefixWord ++ tailWord_4401521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4401539 : List Nat := [1, 1, 1, 3, 6, 2, 1, 2, 2, 1, 3]
def baseStart_4401539 : Nat := 118140960795 + 4401539 * 2 ^ 59
def prefixEnd_4401539 : Nat := 4983230072969 + 3 ^ 40 * 4401539 * 2
def baseEnd_4401539 : Nat := 2260105126510159692120197

theorem tailTrace_4401539 : CollatzResearch.WordTrace tailWord_4401539 prefixEnd_4401539 2260105126510159692120197 := by
  unfold tailWord_4401539
  simp only [CollatzResearch.WordTrace]
  refine ⟨160537316000983400858583671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107024877333988933905722447 160537316000983400858583671)
  ·
    refine ⟨240805974001475101287875507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160537316000983400858583671 240805974001475101287875507)
    ·
      refine ⟨361208961002212651931813261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240805974001475101287875507 361208961002212651931813261)
      ·
        refine ⟨135453360375829744474429973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 361208961002212651931813261 135453360375829744474429973)
        ·
          refine ⟨6349376267617019272238905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 135453360375829744474429973 6349376267617019272238905)
          ·
            refine ⟨4762032200712764454179179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6349376267617019272238905 4762032200712764454179179)
            ·
              refine ⟨7143048301069146681268769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4762032200712764454179179 7143048301069146681268769)
              ·
                refine ⟨5357286225801860010951577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7143048301069146681268769 5357286225801860010951577)
                ·
                  refine ⟨4017964669351395008213683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5357286225801860010951577 4017964669351395008213683)
                  ·
                    refine ⟨6026947004027092512320525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4017964669351395008213683 6026947004027092512320525)
                    ·
                      refine ⟨2260105126510159692120197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6026947004027092512320525 2260105126510159692120197)
                      ·
                        rfl

theorem cell23_4401539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 2, 2, 1, 3].length) (baseStart_4401539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4401539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4401539 prefixEnd_4401539 := by exact prefixLift 4401539
  have htrace : WordTrace (prefixWord ++ tailWord_4401539) baseStart_4401539 baseEnd_4401539 := by
    simpa [prefixWord, tailWord_4401539, baseEnd_4401539] using wordTrace_append hprefix tailTrace_4401539
  have hstable : (prefixWord ++ tailWord_4401539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4401539).length < 2 ^ (prefixWord ++ tailWord_4401539).sum := by decide
  have hdescent : baseEnd_4401539 < baseStart_4401539 := by decide
  rcases family_descends (prefixWord ++ tailWord_4401539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4401556 : List Nat := [2, 4, 2, 1, 3, 1, 3, 1, 2, 1, 3]
def baseStart_4401556 : Nat := 118140960795 + 4401556 * 2 ^ 59
def prefixEnd_4401556 : Nat := 4983230072969 + 3 ^ 40 * 4401556 * 2
def baseEnd_4401556 : Nat := 2260113855681286125607619

theorem tailTrace_4401556 : CollatzResearch.WordTrace tailWord_4401556 prefixEnd_4401556 2260113855681286125607619 := by
  unfold tailWord_4401556
  simp only [CollatzResearch.WordTrace]
  refine ⟨80268968020960906380976261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107025290694614541841301681 80268968020960906380976261)
  ·
    refine ⟨15050431503930169946433049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80268968020960906380976261 15050431503930169946433049)
    ·
      refine ⟨11287823627947627459824787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15050431503930169946433049 11287823627947627459824787)
      ·
        refine ⟨16931735441921441189737181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11287823627947627459824787 16931735441921441189737181)
        ·
          refine ⟨6349400790720540446151443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16931735441921441189737181 6349400790720540446151443)
          ·
            refine ⟨9524101186080810669227165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6349400790720540446151443 9524101186080810669227165)
            ·
              refine ⟨3571537944780304000960187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9524101186080810669227165 3571537944780304000960187)
              ·
                refine ⟨5357306917170456001440281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3571537944780304000960187 5357306917170456001440281)
                ·
                  refine ⟨4017980187877842001080211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5357306917170456001440281 4017980187877842001080211)
                  ·
                    refine ⟨6026970281816763001620317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4017980187877842001080211 6026970281816763001620317)
                    ·
                      refine ⟨2260113855681286125607619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6026970281816763001620317 2260113855681286125607619)
                      ·
                        rfl

theorem cell23_4401556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 3, 1, 2, 1, 3].length) (baseStart_4401556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4401556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4401556 prefixEnd_4401556 := by exact prefixLift 4401556
  have htrace : WordTrace (prefixWord ++ tailWord_4401556) baseStart_4401556 baseEnd_4401556 := by
    simpa [prefixWord, tailWord_4401556, baseEnd_4401556] using wordTrace_append hprefix tailTrace_4401556
  have hstable : (prefixWord ++ tailWord_4401556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4401556).length < 2 ^ (prefixWord ++ tailWord_4401556).sum := by decide
  have hdescent : baseEnd_4401556 < baseStart_4401556 := by decide
  rcases family_descends (prefixWord ++ tailWord_4401556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4401562 : List Nat := [3, 1, 1, 4, 1, 2, 3, 1, 1, 4, 2]
def baseStart_4401562 : Nat := 118140960795 + 4401562 * 2 ^ 59
def prefixEnd_4401562 : Nat := 4983230072969 + 3 ^ 40 * 4401562 * 2
def baseEnd_4401562 : Nat := 2260116936565213102132591

theorem tailTrace_4401562 : CollatzResearch.WordTrace tailWord_4401562 prefixEnd_4401562 2260116936565213102132591 := by
  unfold tailWord_4401562
  simp only [CollatzResearch.WordTrace]
  refine ⟨40134538719975018946667735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107025436586600050524447293 40134538719975018946667735)
  ·
    refine ⟨60201808079962528420001603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40134538719975018946667735 60201808079962528420001603)
    ·
      refine ⟨90302712119943792630002405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60201808079962528420001603 90302712119943792630002405)
      ·
        refine ⟨16931758522489461118125451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90302712119943792630002405 16931758522489461118125451)
        ·
          refine ⟨25397637783734191677188177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16931758522489461118125451 25397637783734191677188177)
          ·
            refine ⟨19048228337800643757891133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25397637783734191677188177 19048228337800643757891133)
            ·
              refine ⟨7143085626675241409209175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19048228337800643757891133 7143085626675241409209175)
              ·
                refine ⟨10714628440012862113813763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7143085626675241409209175 10714628440012862113813763)
                ·
                  refine ⟨16071942660019293170720645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10714628440012862113813763 16071942660019293170720645)
                  ·
                    refine ⟨3013489248753617469510121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16071942660019293170720645 3013489248753617469510121)
                    ·
                      refine ⟨2260116936565213102132591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3013489248753617469510121 2260116936565213102132591)
                      ·
                        rfl

theorem cell23_4401562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 1, 1, 4, 2].length) (baseStart_4401562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4401562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4401562 prefixEnd_4401562 := by exact prefixLift 4401562
  have htrace : WordTrace (prefixWord ++ tailWord_4401562) baseStart_4401562 baseEnd_4401562 := by
    simpa [prefixWord, tailWord_4401562, baseEnd_4401562] using wordTrace_append hprefix tailTrace_4401562
  have hstable : (prefixWord ++ tailWord_4401562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4401562).length < 2 ^ (prefixWord ++ tailWord_4401562).sum := by decide
  have hdescent : baseEnd_4401562 < baseStart_4401562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4401562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4401566 : List Nat := [4, 3, 1, 2, 1, 2, 2, 2, 1, 3, 2]
def baseStart_4401566 : Nat := 118140960795 + 4401566 * 2 ^ 59
def prefixEnd_4401566 : Nat := 4983230072969 + 3 ^ 40 * 4401566 * 2
def baseEnd_4401566 : Nat := 2260118990487831086482573

theorem tailTrace_4401566 : CollatzResearch.WordTrace tailWord_4401566 prefixEnd_4401566 2260118990487831086482573 := by
  unfold tailWord_4401566
  simp only [CollatzResearch.WordTrace]
  refine ⟨20067287596485698058727069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107025533847923722979877701 20067287596485698058727069)
  ·
    refine ⟨7525232848682136772022651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20067287596485698058727069 7525232848682136772022651)
    ·
      refine ⟨11287849273023205158033977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7525232848682136772022651 11287849273023205158033977)
      ·
        refine ⟨8465886954767403868525483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11287849273023205158033977 8465886954767403868525483)
        ·
          refine ⟨12698830432151105802788225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8465886954767403868525483 12698830432151105802788225)
          ·
            refine ⟨9524122824113329352091169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12698830432151105802788225 9524122824113329352091169)
            ·
              refine ⟨7143092118084997014068377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9524122824113329352091169 7143092118084997014068377)
              ·
                refine ⟨5357319088563747760551283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7143092118084997014068377 5357319088563747760551283)
                ·
                  refine ⟨8035978632845621640826925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5357319088563747760551283 8035978632845621640826925)
                  ·
                    refine ⟨3013491987317108115310097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8035978632845621640826925 3013491987317108115310097)
                    ·
                      refine ⟨2260118990487831086482573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3013491987317108115310097 2260118990487831086482573)
                      ·
                        rfl

theorem cell23_4401566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_4401566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4401566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4401566 prefixEnd_4401566 := by exact prefixLift 4401566
  have htrace : WordTrace (prefixWord ++ tailWord_4401566) baseStart_4401566 baseEnd_4401566 := by
    simpa [prefixWord, tailWord_4401566, baseEnd_4401566] using wordTrace_append hprefix tailTrace_4401566
  have hstable : (prefixWord ++ tailWord_4401566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4401566).length < 2 ^ (prefixWord ++ tailWord_4401566).sum := by decide
  have hdescent : baseEnd_4401566 < baseStart_4401566 := by decide
  rcases family_descends (prefixWord ++ tailWord_4401566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4401568 : List Nat := [2, 1, 1, 4, 1, 3, 2, 2, 7]
def baseStart_4401568 : Nat := 118140960795 + 4401568 * 2 ^ 59
def prefixEnd_4401568 : Nat := 4983230072969 + 3 ^ 40 * 4401568 * 2
def baseEnd_4401568 : Nat := 251124446383237786517507

theorem tailTrace_4401568 : CollatzResearch.WordTrace tailWord_4401568 prefixEnd_4401568 251124446383237786517507 := by
  unfold tailWord_4401568
  simp only [CollatzResearch.WordTrace]
  refine ⟨80269186858939169405694679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107025582478585559207592905 80269186858939169405694679)
  ·
    refine ⟨120403780288408754108542019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80269186858939169405694679 120403780288408754108542019)
    ·
      refine ⟨180605670432613131162813029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120403780288408754108542019 180605670432613131162813029)
      ·
        refine ⟨33863563206114962093027443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 180605670432613131162813029 33863563206114962093027443)
        ·
          refine ⟨50795344809172443139541165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33863563206114962093027443 50795344809172443139541165)
          ·
            refine ⟨19048254303439666177327937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50795344809172443139541165 19048254303439666177327937)
            ·
              refine ⟨14286190727579749632995953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19048254303439666177327937 14286190727579749632995953)
              ·
                refine ⟨10714643045684812224746965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14286190727579749632995953 10714643045684812224746965)
                ·
                  refine ⟨251124446383237786517507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10714643045684812224746965 251124446383237786517507)
                  ·
                    rfl

theorem cell23_4401568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 2, 7].length) (baseStart_4401568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4401568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4401568 prefixEnd_4401568 := by exact prefixLift 4401568
  have htrace : WordTrace (prefixWord ++ tailWord_4401568) baseStart_4401568 baseEnd_4401568 := by
    simpa [prefixWord, tailWord_4401568, baseEnd_4401568] using wordTrace_append hprefix tailTrace_4401568
  have hstable : (prefixWord ++ tailWord_4401568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4401568).length < 2 ^ (prefixWord ++ tailWord_4401568).sum := by decide
  have hdescent : baseEnd_4401568 < baseStart_4401568 := by decide
  rcases family_descends (prefixWord ++ tailWord_4401568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4401608 : List Nat := [2, 1, 3, 1, 3, 2, 1, 1, 1, 1, 7]
def baseStart_4401608 : Nat := 118140960795 + 4401608 * 2 ^ 59
def prefixEnd_4401608 : Nat := 4983230072969 + 3 ^ 40 * 4401608 * 2
def baseEnd_4401608 : Nat := 2260140556675319922157379

theorem tailTrace_4401608 : CollatzResearch.WordTrace tailWord_4401608 prefixEnd_4401608 2260140556675319922157379 := by
  unfold tailWord_4401608
  simp only [CollatzResearch.WordTrace]
  refine ⟨80269916318866712821422739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107026555091822283761896985 80269916318866712821422739)
  ·
    refine ⟨120404874478300069232134109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80269916318866712821422739 120404874478300069232134109)
    ·
      refine ⟨45151827929362525962050291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120404874478300069232134109 45151827929362525962050291)
      ·
        refine ⟨67727741894043788943075437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45151827929362525962050291 67727741894043788943075437)
        ·
          refine ⟨25397903210266420853653289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67727741894043788943075437 25397903210266420853653289)
          ·
            refine ⟨19048427407699815640239967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25397903210266420853653289 19048427407699815640239967)
            ·
              refine ⟨28572641111549723460359951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19048427407699815640239967 28572641111549723460359951)
              ·
                refine ⟨42858961667324585190539927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28572641111549723460359951 42858961667324585190539927)
                ·
                  refine ⟨64288442500986877785809891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42858961667324585190539927 64288442500986877785809891)
                  ·
                    refine ⟨96432663751480316678714837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 64288442500986877785809891 96432663751480316678714837)
                    ·
                      refine ⟨2260140556675319922157379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 96432663751480316678714837 2260140556675319922157379)
                      ·
                        rfl

theorem cell23_4401608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 1, 1, 7].length) (baseStart_4401608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4401608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4401608 prefixEnd_4401608 := by exact prefixLift 4401608
  have htrace : WordTrace (prefixWord ++ tailWord_4401608) baseStart_4401608 baseEnd_4401608 := by
    simpa [prefixWord, tailWord_4401608, baseEnd_4401608] using wordTrace_append hprefix tailTrace_4401608
  have hstable : (prefixWord ++ tailWord_4401608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4401608).length < 2 ^ (prefixWord ++ tailWord_4401608).sum := by decide
  have hdescent : baseEnd_4401608 < baseStart_4401608 := by decide
  rcases family_descends (prefixWord ++ tailWord_4401608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4401648 : List Nat := [2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 6]
def baseStart_4401648 : Nat := 118140960795 + 4401648 * 2 ^ 59
def prefixEnd_4401648 : Nat := 4983230072969 + 3 ^ 40 * 4401648 * 2
def baseEnd_4401648 : Nat := 2260161095901499765657195

theorem tailTrace_4401648 : CollatzResearch.WordTrace tailWord_4401648 prefixEnd_4401648 2260161095901499765657195 := by
  unfold tailWord_4401648
  simp only [CollatzResearch.WordTrace]
  refine ⟨80270645778794256237150799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107027527705059008316201065 80270645778794256237150799)
  ·
    refine ⟨120405968668191384355726199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80270645778794256237150799 120405968668191384355726199)
    ·
      refine ⟨180608953002287076533589299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120405968668191384355726199 180608953002287076533589299)
      ·
        refine ⟨270913429503430614800383949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180608953002287076533589299 270913429503430614800383949)
        ·
          refine ⟨101592536063786480550143981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 270913429503430614800383949 101592536063786480550143981)
          ·
            refine ⟨38097201023919930206303993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101592536063786480550143981 38097201023919930206303993)
            ·
              refine ⟨28572900767939947654727995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38097201023919930206303993 28572900767939947654727995)
              ·
                refine ⟨42859351151909921482091993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28572900767939947654727995 42859351151909921482091993)
                ·
                  refine ⟨32144513363932441111568995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42859351151909921482091993 32144513363932441111568995)
                  ·
                    refine ⟨48216770045898661667353493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32144513363932441111568995 48216770045898661667353493)
                    ·
                      refine ⟨2260161095901499765657195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48216770045898661667353493 2260161095901499765657195)
                      ·
                        rfl

theorem cell23_4401648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 6].length) (baseStart_4401648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4401648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4401648 prefixEnd_4401648 := by exact prefixLift 4401648
  have htrace : WordTrace (prefixWord ++ tailWord_4401648) baseStart_4401648 baseEnd_4401648 := by
    simpa [prefixWord, tailWord_4401648, baseEnd_4401648] using wordTrace_append hprefix tailTrace_4401648
  have hstable : (prefixWord ++ tailWord_4401648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4401648).length < 2 ^ (prefixWord ++ tailWord_4401648).sum := by decide
  have hdescent : baseEnd_4401648 < baseStart_4401648 := by decide
  rcases family_descends (prefixWord ++ tailWord_4401648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4401653 : List Nat := [1, 3, 5, 1, 3, 1, 2, 2, 5]
def baseStart_4401653 : Nat := 118140960795 + 4401653 * 2 ^ 59
def prefixEnd_4401653 : Nat := 4983230072969 + 3 ^ 40 * 4401653 * 2
def baseEnd_4401653 : Nat := 251129295922752471788297

theorem tailTrace_4401653 : CollatzResearch.WordTrace tailWord_4401653 prefixEnd_4401653 251129295922752471788297 := by
  unfold tailWord_4401653
  simp only [CollatzResearch.WordTrace]
  refine ⟨160541473922570398328233613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107027649281713598885489075 160541473922570398328233613)
  ·
    refine ⟨60203052720963899373087605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160541473922570398328233613 60203052720963899373087605)
    ·
      refine ⟨5644036192590365566226963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 60203052720963899373087605 5644036192590365566226963)
      ·
        refine ⟨8466054288885548349340445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5644036192590365566226963 8466054288885548349340445)
        ·
          refine ⟨3174770358332080631002667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8466054288885548349340445 3174770358332080631002667)
          ·
            refine ⟨4762155537498120946504001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3174770358332080631002667 4762155537498120946504001)
            ·
              refine ⟨3571616653123590709878001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4762155537498120946504001 3571616653123590709878001)
              ·
                refine ⟨2678712489842693032408501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3571616653123590709878001 2678712489842693032408501)
                ·
                  refine ⟨251129295922752471788297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2678712489842693032408501 251129295922752471788297)
                  ·
                    rfl

theorem cell23_4401653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 2, 2, 5].length) (baseStart_4401653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4401653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4401653 prefixEnd_4401653 := by exact prefixLift 4401653
  have htrace : WordTrace (prefixWord ++ tailWord_4401653) baseStart_4401653 baseEnd_4401653 := by
    simpa [prefixWord, tailWord_4401653, baseEnd_4401653] using wordTrace_append hprefix tailTrace_4401653
  have hstable : (prefixWord ++ tailWord_4401653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4401653).length < 2 ^ (prefixWord ++ tailWord_4401653).sum := by decide
  have hdescent : baseEnd_4401653 < baseStart_4401653 := by decide
  rcases family_descends (prefixWord ++ tailWord_4401653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4401675 : List Nat := [1, 1, 1, 1, 7, 1, 2, 3, 6]
def baseStart_4401675 : Nat := 118140960795 + 4401675 * 2 ^ 59
def prefixEnd_4401675 : Nat := 4983230072969 + 3 ^ 40 * 4401675 * 2
def baseEnd_4401675 : Nat := 251130551097685684446619

theorem tailTrace_4401675 : CollatzResearch.WordTrace tailWord_4401675 prefixEnd_4401675 251130551097685684446619 := by
  unfold tailWord_4401675
  simp only [CollatzResearch.WordTrace]
  refine ⟨160542276328490696085534479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107028184218993797390356319 160542276328490696085534479)
  ·
    refine ⟨240813414492736044128301719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160542276328490696085534479 240813414492736044128301719)
    ·
      refine ⟨361220121739104066192452579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240813414492736044128301719 361220121739104066192452579)
      ·
        refine ⟨541830182608656099288678869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 361220121739104066192452579 541830182608656099288678869)
        ·
          refine ⟨12699144904890377327078411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 541830182608656099288678869 12699144904890377327078411)
          ·
            refine ⟨19048717357335565990617617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12699144904890377327078411 19048717357335565990617617)
            ·
              refine ⟨14286538018001674492963213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19048717357335565990617617 14286538018001674492963213)
              ·
                refine ⟨5357451756750627934861205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14286538018001674492963213 5357451756750627934861205)
                ·
                  refine ⟨251130551097685684446619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5357451756750627934861205 251130551097685684446619)
                  ·
                    rfl

theorem cell23_4401675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 3, 6].length) (baseStart_4401675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4401675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4401675 prefixEnd_4401675 := by exact prefixLift 4401675
  have htrace : WordTrace (prefixWord ++ tailWord_4401675) baseStart_4401675 baseEnd_4401675 := by
    simpa [prefixWord, tailWord_4401675, baseEnd_4401675] using wordTrace_append hprefix tailTrace_4401675
  have hstable : (prefixWord ++ tailWord_4401675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4401675).length < 2 ^ (prefixWord ++ tailWord_4401675).sum := by decide
  have hdescent : baseEnd_4401675 < baseStart_4401675 := by decide
  rcases family_descends (prefixWord ++ tailWord_4401675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4401696 : List Nat := [2, 1, 1, 6, 2, 1, 2, 3, 1, 4]
def baseStart_4401696 : Nat := 118140960795 + 4401696 * 2 ^ 59
def prefixEnd_4401696 : Nat := 4983230072969 + 3 ^ 40 * 4401696 * 2
def baseEnd_4401696 : Nat := 753395247657638525952325

theorem tailTrace_4401696 : CollatzResearch.WordTrace tailWord_4401696 prefixEnd_4401696 753395247657638525952325 := by
  unfold tailWord_4401696
  simp only [CollatzResearch.WordTrace]
  refine ⟨80271521130707308336024471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107028694840943077781365961 80271521130707308336024471)
  ·
    refine ⟨120407281696060962504036707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80271521130707308336024471 120407281696060962504036707)
    ·
      refine ⟨180610922544091443756055061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120407281696060962504036707 180610922544091443756055061)
      ·
        refine ⟨8466136994254286426065081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 180610922544091443756055061 8466136994254286426065081)
        ·
          refine ⟨6349602745690714819548811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8466136994254286426065081 6349602745690714819548811)
          ·
            refine ⟨9524404118536072229323217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6349602745690714819548811 9524404118536072229323217)
            ·
              refine ⟨7143303088902054171992413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9524404118536072229323217 7143303088902054171992413)
              ·
                refine ⟨2678738658338270314497155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7143303088902054171992413 2678738658338270314497155)
                ·
                  refine ⟨4018107987507405471745733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2678738658338270314497155 4018107987507405471745733)
                  ·
                    refine ⟨753395247657638525952325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4018107987507405471745733 753395247657638525952325)
                    ·
                      rfl

theorem cell23_4401696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 3, 1, 4].length) (baseStart_4401696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4401696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4401696 prefixEnd_4401696 := by exact prefixLift 4401696
  have htrace : WordTrace (prefixWord ++ tailWord_4401696) baseStart_4401696 baseEnd_4401696 := by
    simpa [prefixWord, tailWord_4401696, baseEnd_4401696] using wordTrace_append hprefix tailTrace_4401696
  have hstable : (prefixWord ++ tailWord_4401696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4401696).length < 2 ^ (prefixWord ++ tailWord_4401696).sum := by decide
  have hdescent : baseEnd_4401696 < baseStart_4401696 := by decide
  rcases family_descends (prefixWord ++ tailWord_4401696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4401712 : List Nat := [2, 1, 1, 1, 2, 3, 2, 4, 2, 3, 2]
def baseStart_4401712 : Nat := 118140960795 + 4401712 * 2 ^ 59
def prefixEnd_4401712 : Nat := 4983230072969 + 3 ^ 40 * 4401712 * 2
def baseEnd_4401712 : Nat := 2260193958663387515256901

theorem tailTrace_4401712 : CollatzResearch.WordTrace tailWord_4401712 prefixEnd_4401712 2260193958663387515256901 := by
  unfold tailWord_4401712
  simp only [CollatzResearch.WordTrace]
  refine ⟨80271812914678325702315695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107029083886237767603087593 80271812914678325702315695)
  ·
    refine ⟨120407719372017488553473543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80271812914678325702315695 120407719372017488553473543)
    ·
      refine ⟨180611579058026232830210315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120407719372017488553473543 180611579058026232830210315)
      ·
        refine ⟨270917368587039349245315473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180611579058026232830210315 270917368587039349245315473)
        ·
          refine ⟨203188026440279511933986605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 270917368587039349245315473 203188026440279511933986605)
          ·
            refine ⟨76195509915104816975244977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 203188026440279511933986605 76195509915104816975244977)
            ·
              refine ⟨57146632436328612731433733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76195509915104816975244977 57146632436328612731433733)
              ·
                refine ⟨10714993581811614887143825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57146632436328612731433733 10714993581811614887143825)
                ·
                  refine ⟨8036245186358711165357869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10714993581811614887143825 8036245186358711165357869)
                  ·
                    refine ⟨3013591944884516687009201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8036245186358711165357869 3013591944884516687009201)
                    ·
                      refine ⟨2260193958663387515256901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3013591944884516687009201 2260193958663387515256901)
                      ·
                        rfl

theorem cell23_4401712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 4, 2, 3, 2].length) (baseStart_4401712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4401712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4401712 prefixEnd_4401712 := by exact prefixLift 4401712
  have htrace : WordTrace (prefixWord ++ tailWord_4401712) baseStart_4401712 baseEnd_4401712 := by
    simpa [prefixWord, tailWord_4401712, baseEnd_4401712] using wordTrace_append hprefix tailTrace_4401712
  have hstable : (prefixWord ++ tailWord_4401712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4401712).length < 2 ^ (prefixWord ++ tailWord_4401712).sum := by decide
  have hdescent : baseEnd_4401712 < baseStart_4401712 := by decide
  rcases family_descends (prefixWord ++ tailWord_4401712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4401719 : List Nat := [1, 1, 3, 1, 2, 3, 1, 6, 1, 1, 3]
def baseStart_4401719 : Nat := 118140960795 + 4401719 * 2 ^ 59
def prefixEnd_4401719 : Nat := 4983230072969 + 3 ^ 40 * 4401719 * 2
def baseEnd_4401719 : Nat := 2260197553027968987869369

theorem tailTrace_4401719 : CollatzResearch.WordTrace tailWord_4401719 prefixEnd_4401719 2260197553027968987869369 := by
  unfold tailWord_4401719
  simp only [CollatzResearch.WordTrace]
  refine ⟨160543881140331291600136211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107029254093554194400090807 160543881140331291600136211)
  ·
    refine ⟨240815821710496937400204317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160543881140331291600136211 240815821710496937400204317)
    ·
      refine ⟨90305933141436351525076619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 240815821710496937400204317 90305933141436351525076619)
      ·
        refine ⟨135458899712154527287614929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90305933141436351525076619 135458899712154527287614929)
        ·
          refine ⟨101594174784115895465711197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135458899712154527287614929 101594174784115895465711197)
          ·
            refine ⟨38097815544043460799641699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101594174784115895465711197 38097815544043460799641699)
            ·
              refine ⟨57146723316065191199462549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38097815544043460799641699 57146723316065191199462549)
              ·
                refine ⟨2678752655440555837474807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 57146723316065191199462549 2678752655440555837474807)
                ·
                  refine ⟨4018128983160833756212211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2678752655440555837474807 4018128983160833756212211)
                  ·
                    refine ⟨6027193474741250634318317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4018128983160833756212211 6027193474741250634318317)
                    ·
                      refine ⟨2260197553027968987869369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6027193474741250634318317 2260197553027968987869369)
                      ·
                        rfl

theorem cell23_4401719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 6, 1, 1, 3].length) (baseStart_4401719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4401719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4401719 prefixEnd_4401719 := by exact prefixLift 4401719
  have htrace : WordTrace (prefixWord ++ tailWord_4401719) baseStart_4401719 baseEnd_4401719 := by
    simpa [prefixWord, tailWord_4401719, baseEnd_4401719] using wordTrace_append hprefix tailTrace_4401719
  have hstable : (prefixWord ++ tailWord_4401719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4401719).length < 2 ^ (prefixWord ++ tailWord_4401719).sum := by decide
  have hdescent : baseEnd_4401719 < baseStart_4401719 := by decide
  rcases family_descends (prefixWord ++ tailWord_4401719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4401726 : List Nat := [4, 2, 1, 4, 1, 1, 3, 1, 6]
def baseStart_4401726 : Nat := 118140960795 + 4401726 * 2 ^ 59
def prefixEnd_4401726 : Nat := 4983230072969 + 3 ^ 40 * 4401726 * 2
def baseEnd_4401726 : Nat := 251133460821394495609093

theorem tailTrace_4401726 : CollatzResearch.WordTrace tailWord_4401726 prefixEnd_4401726 251133460821394495609093 := by
  unfold tailWord_4401726
  simp only [CollatzResearch.WordTrace]
  refine ⟨20068017056413241474455129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107029424300870621197094021 20068017056413241474455129)
  ·
    refine ⟨15051012792309931105841347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20068017056413241474455129 15051012792309931105841347)
    ·
      refine ⟨22576519188464896658762021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15051012792309931105841347 22576519188464896658762021)
      ·
        refine ⟨4233097347837168123517879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22576519188464896658762021 4233097347837168123517879)
        ·
          refine ⟨6349646021755752185276819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4233097347837168123517879 6349646021755752185276819)
          ·
            refine ⟨9524469032633628277915229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6349646021755752185276819 9524469032633628277915229)
            ·
              refine ⟨3571675887237610604218211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9524469032633628277915229 3571675887237610604218211)
              ·
                refine ⟨5357513830856415906327317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3571675887237610604218211 5357513830856415906327317)
                ·
                  refine ⟨251133460821394495609093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5357513830856415906327317 251133460821394495609093)
                  ·
                    rfl

theorem cell23_4401726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 3, 1, 6].length) (baseStart_4401726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4401726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4401726 prefixEnd_4401726 := by exact prefixLift 4401726
  have htrace : WordTrace (prefixWord ++ tailWord_4401726) baseStart_4401726 baseEnd_4401726 := by
    simpa [prefixWord, tailWord_4401726, baseEnd_4401726] using wordTrace_append hprefix tailTrace_4401726
  have hstable : (prefixWord ++ tailWord_4401726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4401726).length < 2 ^ (prefixWord ++ tailWord_4401726).sum := by decide
  have hdescent : baseEnd_4401726 < baseStart_4401726 := by decide
  rcases family_descends (prefixWord ++ tailWord_4401726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4401742 : List Nat := [4, 1, 1, 1, 1, 2, 3, 4, 1, 1, 4]
def baseStart_4401742 : Nat := 118140960795 + 4401742 * 2 ^ 59
def prefixEnd_4401742 : Nat := 4983230072969 + 3 ^ 40 * 4401742 * 2
def baseEnd_4401742 : Nat := 2260209363083022397881763

theorem tailTrace_4401742 : CollatzResearch.WordTrace tailWord_4401742 prefixEnd_4401742 2260209363083022397881763 := by
  unfold tailWord_4401742
  simp only [CollatzResearch.WordTrace]
  refine ⟨20068090002405995816027935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107029813346165311018815653 20068090002405995816027935)
  ·
    refine ⟨30102135003608993724041903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20068090002405995816027935 30102135003608993724041903)
    ·
      refine ⟨45153202505413490586062855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30102135003608993724041903 45153202505413490586062855)
      ·
        refine ⟨67729803758120235879094283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45153202505413490586062855 67729803758120235879094283)
        ·
          refine ⟨101594705637180353818641425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67729803758120235879094283 101594705637180353818641425)
          ·
            refine ⟨76196029227885265363981069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101594705637180353818641425 76196029227885265363981069)
            ·
              refine ⟨28573510960456974511492901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76196029227885265363981069 28573510960456974511492901)
              ·
                refine ⟨5357533305085682720904919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28573510960456974511492901 5357533305085682720904919)
                ·
                  refine ⟨8036299957628524081357379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5357533305085682720904919 8036299957628524081357379)
                  ·
                    refine ⟨12054449936442786122036069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8036299957628524081357379 12054449936442786122036069)
                    ·
                      refine ⟨2260209363083022397881763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12054449936442786122036069 2260209363083022397881763)
                      ·
                        rfl

theorem cell23_4401742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 4, 1, 1, 4].length) (baseStart_4401742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4401742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4401742 prefixEnd_4401742 := by exact prefixLift 4401742
  have htrace : WordTrace (prefixWord ++ tailWord_4401742) baseStart_4401742 baseEnd_4401742 := by
    simpa [prefixWord, tailWord_4401742, baseEnd_4401742] using wordTrace_append hprefix tailTrace_4401742
  have hstable : (prefixWord ++ tailWord_4401742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4401742).length < 2 ^ (prefixWord ++ tailWord_4401742).sum := by decide
  have hdescent : baseEnd_4401742 < baseStart_4401742 := by decide
  rcases family_descends (prefixWord ++ tailWord_4401742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4401796 : List Nat := [2, 3, 2, 1, 3, 3, 1, 2, 1, 2, 3]
def baseStart_4401796 : Nat := 118140960795 + 4401796 * 2 ^ 59
def prefixEnd_4401796 : Nat := 4983230072969 + 3 ^ 40 * 4401796 * 2
def baseEnd_4401796 : Nat := 2260237091038365186606515

theorem tailTrace_4401796 : CollatzResearch.WordTrace tailWord_4401796 prefixEnd_4401796 2260237091038365186606515 := by
  unfold tailWord_4401796
  simp only [CollatzResearch.WordTrace]
  refine ⟨80273344780526166875344621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107031126374034889167126161 80273344780526166875344621)
  ·
    refine ⟨30102504292697312578254233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80273344780526166875344621 30102504292697312578254233)
    ·
      refine ⟨22576878219522984433690675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30102504292697312578254233 22576878219522984433690675)
      ·
        refine ⟨33865317329284476650536013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22576878219522984433690675 33865317329284476650536013)
        ·
          refine ⟨12699493998481678743951005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33865317329284476650536013 12699493998481678743951005)
          ·
            refine ⟨4762310249430629528981627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12699493998481678743951005 4762310249430629528981627)
            ·
              refine ⟨7143465374145944293472441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4762310249430629528981627 7143465374145944293472441)
              ·
                refine ⟨5357599030609458220104331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7143465374145944293472441 5357599030609458220104331)
                ·
                  refine ⟨8036398545914187330156497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5357599030609458220104331 8036398545914187330156497)
                  ·
                    refine ⟨6027298909435640497617373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8036398545914187330156497 6027298909435640497617373)
                    ·
                      refine ⟨2260237091038365186606515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6027298909435640497617373 2260237091038365186606515)
                      ·
                        rfl

theorem cell23_4401796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 2, 1, 2, 3].length) (baseStart_4401796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4401796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4401796 prefixEnd_4401796 := by exact prefixLift 4401796
  have htrace : WordTrace (prefixWord ++ tailWord_4401796) baseStart_4401796 baseEnd_4401796 := by
    simpa [prefixWord, tailWord_4401796, baseEnd_4401796] using wordTrace_append hprefix tailTrace_4401796
  have hstable : (prefixWord ++ tailWord_4401796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4401796).length < 2 ^ (prefixWord ++ tailWord_4401796).sum := by decide
  have hdescent : baseEnd_4401796 < baseStart_4401796 := by decide
  rcases family_descends (prefixWord ++ tailWord_4401796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4401849 : List Nat := [1, 2, 1, 4, 1, 1, 1, 2, 6, 2, 2]
def baseStart_4401849 : Nat := 118140960795 + 4401849 * 2 ^ 59
def prefixEnd_4401849 : Nat := 4983230072969 + 3 ^ 40 * 4401849 * 2
def baseEnd_4401849 : Nat := 2260264305513053479243771

theorem tailTrace_4401849 : CollatzResearch.WordTrace tailWord_4401849 prefixEnd_4401849 2260264305513053479243771 := by
  unfold tailWord_4401849
  simp only [CollatzResearch.WordTrace]
  refine ⟨160548622629860323802368601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107032415086573549201579067 160548622629860323802368601)
  ·
    refine ⟨120411466972395242851776451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160548622629860323802368601 120411466972395242851776451)
    ·
      refine ⟨180617200458592864277664677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120411466972395242851776451 180617200458592864277664677)
      ·
        refine ⟨33865725085986162052062127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 180617200458592864277664677 33865725085986162052062127)
        ·
          refine ⟨50798587628979243078093191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33865725085986162052062127 50798587628979243078093191)
          ·
            refine ⟨76197881443468864617139787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50798587628979243078093191 76197881443468864617139787)
            ·
              refine ⟨114296822165203296925709681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76197881443468864617139787 114296822165203296925709681)
              ·
                refine ⟨85722616623902472694282261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114296822165203296925709681 85722616623902472694282261)
                ·
                  refine ⟨4018247654245428407544481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 85722616623902472694282261 4018247654245428407544481)
                  ·
                    refine ⟨3013685740684071305658361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4018247654245428407544481 3013685740684071305658361)
                    ·
                      refine ⟨2260264305513053479243771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3013685740684071305658361 2260264305513053479243771)
                      ·
                        rfl

theorem cell23_4401849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 6, 2, 2].length) (baseStart_4401849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4401849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4401849 prefixEnd_4401849 := by exact prefixLift 4401849
  have htrace : WordTrace (prefixWord ++ tailWord_4401849) baseStart_4401849 baseEnd_4401849 := by
    simpa [prefixWord, tailWord_4401849, baseEnd_4401849] using wordTrace_append hprefix tailTrace_4401849
  have hstable : (prefixWord ++ tailWord_4401849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4401849).length < 2 ^ (prefixWord ++ tailWord_4401849).sum := by decide
  have hdescent : baseEnd_4401849 < baseStart_4401849 := by decide
  rcases family_descends (prefixWord ++ tailWord_4401849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4401852 : List Nat := [2, 2, 2, 3, 1, 1, 1, 2, 2, 4, 3]
def baseStart_4401852 : Nat := 118140960795 + 4401852 * 2 ^ 59
def prefixEnd_4401852 : Nat := 4983230072969 + 3 ^ 40 * 4401852 * 2
def baseEnd_4401852 : Nat := 2260265845955016967506257

theorem tailTrace_4401852 : CollatzResearch.WordTrace tailWord_4401852 prefixEnd_4401852 2260265845955016967506257 := by
  unfold tailWord_4401852
  simp only [CollatzResearch.WordTrace]
  refine ⟨80274366024424727657363905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107032488032566303543151873 80274366024424727657363905)
  ·
    refine ⟨60205774518318545743022929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80274366024424727657363905 60205774518318545743022929)
    ·
      refine ⟨45154330888738909307267197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60205774518318545743022929 45154330888738909307267197)
      ·
        refine ⟨16932874083277090990225199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45154330888738909307267197 16932874083277090990225199)
        ·
          refine ⟨25399311124915636485337799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16932874083277090990225199 25399311124915636485337799)
          ·
            refine ⟨38098966687373454728006699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25399311124915636485337799 38098966687373454728006699)
            ·
              refine ⟨57148450031060182092010049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38098966687373454728006699 57148450031060182092010049)
              ·
                refine ⟨42861337523295136569007537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57148450031060182092010049 42861337523295136569007537)
                ·
                  refine ⟨32146003142471352426755653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42861337523295136569007537 32146003142471352426755653)
                  ·
                    refine ⟨6027375589213378580016685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32146003142471352426755653 6027375589213378580016685)
                    ·
                      refine ⟨2260265845955016967506257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6027375589213378580016685 2260265845955016967506257)
                      ·
                        rfl

theorem cell23_4401852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_4401852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4401852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4401852 prefixEnd_4401852 := by exact prefixLift 4401852
  have htrace : WordTrace (prefixWord ++ tailWord_4401852) baseStart_4401852 baseEnd_4401852 := by
    simpa [prefixWord, tailWord_4401852, baseEnd_4401852] using wordTrace_append hprefix tailTrace_4401852
  have hstable : (prefixWord ++ tailWord_4401852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4401852).length < 2 ^ (prefixWord ++ tailWord_4401852).sum := by decide
  have hdescent : baseEnd_4401852 < baseStart_4401852 := by decide
  rcases family_descends (prefixWord ++ tailWord_4401852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4401855 : List Nat := [1, 1, 2, 2, 2, 4, 1, 1, 9]
def baseStart_4401855 : Nat := 118140960795 + 4401855 * 2 ^ 59
def prefixEnd_4401855 : Nat := 4983230072969 + 3 ^ 40 * 4401855 * 2
def baseEnd_4401855 : Nat := 251140820710775606196527

theorem tailTrace_4401855 : CollatzResearch.WordTrace tailWord_4401855 prefixEnd_4401855 251140820710775606196527 := by
  unfold tailWord_4401855
  simp only [CollatzResearch.WordTrace]
  refine ⟨160548841467838586827087019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107032560978559057884724679 160548841467838586827087019)
  ·
    refine ⟨240823262201757880240630529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160548841467838586827087019 240823262201757880240630529)
    ·
      refine ⟨180617446651318410180472897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 240823262201757880240630529 180617446651318410180472897)
      ·
        refine ⟨135463084988488807635354673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180617446651318410180472897 135463084988488807635354673)
        ·
          refine ⟨101597313741366605726516005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135463084988488807635354673 101597313741366605726516005)
          ·
            refine ⟨19049496326506238573721751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 101597313741366605726516005 19049496326506238573721751)
            ·
              refine ⟨28574244489759357860582627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19049496326506238573721751 28574244489759357860582627)
              ·
                refine ⟨42861366734639036790873941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28574244489759357860582627 42861366734639036790873941)
                ·
                  refine ⟨251140820710775606196527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 42861366734639036790873941 251140820710775606196527)
                  ·
                    rfl

theorem cell23_4401855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 9].length) (baseStart_4401855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4401855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4401855 prefixEnd_4401855 := by exact prefixLift 4401855
  have htrace : WordTrace (prefixWord ++ tailWord_4401855) baseStart_4401855 baseEnd_4401855 := by
    simpa [prefixWord, tailWord_4401855, baseEnd_4401855] using wordTrace_append hprefix tailTrace_4401855
  have hstable : (prefixWord ++ tailWord_4401855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4401855).length < 2 ^ (prefixWord ++ tailWord_4401855).sum := by decide
  have hdescent : baseEnd_4401855 < baseStart_4401855 := by decide
  rcases family_descends (prefixWord ++ tailWord_4401855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4401882 : List Nat := [3, 1, 1, 2, 2, 2, 1, 1, 4, 3, 3]
def baseStart_4401882 : Nat := 118140960795 + 4401882 * 2 ^ 59
def prefixEnd_4401882 : Nat := 4983230072969 + 3 ^ 40 * 4401882 * 2
def baseEnd_4401882 : Nat := 2260281250374651850131119

theorem tailTrace_4401882 : CollatzResearch.WordTrace tailWord_4401882 prefixEnd_4401882 2260281250374651850131119 := by
  unfold tailWord_4401882
  simp only [CollatzResearch.WordTrace]
  refine ⟨40137456559685192609579975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107033217492493846958879933 40137456559685192609579975)
  ·
    refine ⟨60206184839527788914369963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40137456559685192609579975 60206184839527788914369963)
    ·
      refine ⟨90309277259291683371554945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60206184839527788914369963 90309277259291683371554945)
      ·
        refine ⟨67731957944468762528666209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90309277259291683371554945 67731957944468762528666209)
        ·
          refine ⟨50798968458351571896499657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67731957944468762528666209 50798968458351571896499657)
          ·
            refine ⟨38099226343763678922374743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50798968458351571896499657 38099226343763678922374743)
            ·
              refine ⟨57148839515645518383562115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38099226343763678922374743 57148839515645518383562115)
              ·
                refine ⟨85723259273468277575343173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57148839515645518383562115 85723259273468277575343173)
                ·
                  refine ⟨16073111113775302045376845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 85723259273468277575343173 16073111113775302045376845)
                  ·
                    refine ⟨6027416667665738267016317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16073111113775302045376845 6027416667665738267016317)
                    ·
                      refine ⟨2260281250374651850131119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6027416667665738267016317 2260281250374651850131119)
                      ·
                        rfl

theorem cell23_4401882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 4, 3, 3].length) (baseStart_4401882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4401882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4401882 prefixEnd_4401882 := by exact prefixLift 4401882
  have htrace : WordTrace (prefixWord ++ tailWord_4401882) baseStart_4401882 baseEnd_4401882 := by
    simpa [prefixWord, tailWord_4401882, baseEnd_4401882] using wordTrace_append hprefix tailTrace_4401882
  have hstable : (prefixWord ++ tailWord_4401882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4401882).length < 2 ^ (prefixWord ++ tailWord_4401882).sum := by decide
  have hdescent : baseEnd_4401882 < baseStart_4401882 := by decide
  rcases family_descends (prefixWord ++ tailWord_4401882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4401889 : List Nat := [1, 2, 3, 1, 4, 1, 2, 4, 5]
def baseStart_4401889 : Nat := 118140960795 + 4401889 * 2 ^ 59
def prefixEnd_4401889 : Nat := 4983230072969 + 3 ^ 40 * 4401889 * 2
def baseEnd_4401889 : Nat := 251142760526581480304843

theorem tailTrace_4401889 : CollatzResearch.WordTrace tailWord_4401889 prefixEnd_4401889 251142760526581480304843 := by
  unfold tailWord_4401889
  simp only [CollatzResearch.WordTrace]
  refine ⟨160550081549715410633824721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107033387699810273755883147 160550081549715410633824721)
  ·
    refine ⟨120412561162286557975368541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160550081549715410633824721 120412561162286557975368541)
    ·
      refine ⟨45154710435857459240763203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120412561162286557975368541 45154710435857459240763203)
      ·
        refine ⟨67732065653786188861144805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45154710435857459240763203 67732065653786188861144805)
        ·
          refine ⟨12699762310084910411464651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67732065653786188861144805 12699762310084910411464651)
          ·
            refine ⟨19049643465127365617196977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12699762310084910411464651 19049643465127365617196977)
            ·
              refine ⟨14287232598845524212897733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19049643465127365617196977 14287232598845524212897733)
              ·
                refine ⟨2678856112283535789918325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14287232598845524212897733 2678856112283535789918325)
                ·
                  refine ⟨251142760526581480304843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2678856112283535789918325 251142760526581480304843)
                  ·
                    rfl

theorem cell23_4401889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 4, 5].length) (baseStart_4401889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4401889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4401889 prefixEnd_4401889 := by exact prefixLift 4401889
  have htrace : WordTrace (prefixWord ++ tailWord_4401889) baseStart_4401889 baseEnd_4401889 := by
    simpa [prefixWord, tailWord_4401889, baseEnd_4401889] using wordTrace_append hprefix tailTrace_4401889
  have hstable : (prefixWord ++ tailWord_4401889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4401889).length < 2 ^ (prefixWord ++ tailWord_4401889).sum := by decide
  have hdescent : baseEnd_4401889 < baseStart_4401889 := by decide
  rcases family_descends (prefixWord ++ tailWord_4401889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4401902 : List Nat := [4, 1, 2, 1, 1, 3, 1, 2, 1, 7]
def baseStart_4401902 : Nat := 118140960795 + 4401902 * 2 ^ 59
def prefixEnd_4401902 : Nat := 4983230072969 + 3 ^ 40 * 4401902 * 2
def baseEnd_4401902 : Nat := 753430506662580590627009

theorem tailTrace_4401902 : CollatzResearch.WordTrace tailWord_4401902 prefixEnd_4401902 753430506662580590627009 := by
  unfold tailWord_4401902
  simp only [CollatzResearch.WordTrace]
  refine ⟨20068819462333539231755995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107033703799112209236031973 20068819462333539231755995)
  ·
    refine ⟨30103229193500308847633993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20068819462333539231755995 30103229193500308847633993)
    ·
      refine ⟨22577421895125231635725495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30103229193500308847633993 22577421895125231635725495)
      ·
        refine ⟨33866132842687847453588243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22577421895125231635725495 33866132842687847453588243)
        ·
          refine ⟨50799199264031771180382365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33866132842687847453588243 50799199264031771180382365)
          ·
            refine ⟨19049699724011914192643387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50799199264031771180382365 19049699724011914192643387)
            ·
              refine ⟨28574549586017871288965081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19049699724011914192643387 28574549586017871288965081)
              ·
                refine ⟨21430912189513403466723811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28574549586017871288965081 21430912189513403466723811)
                ·
                  refine ⟨32146368284270105200085717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21430912189513403466723811 32146368284270105200085717)
                  ·
                    refine ⟨753430506662580590627009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32146368284270105200085717 753430506662580590627009)
                    ·
                      rfl

theorem cell23_4401902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_4401902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4401902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4401902 prefixEnd_4401902 := by exact prefixLift 4401902
  have htrace : WordTrace (prefixWord ++ tailWord_4401902) baseStart_4401902 baseEnd_4401902 := by
    simpa [prefixWord, tailWord_4401902, baseEnd_4401902] using wordTrace_append hprefix tailTrace_4401902
  have hstable : (prefixWord ++ tailWord_4401902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4401902).length < 2 ^ (prefixWord ++ tailWord_4401902).sum := by decide
  have hdescent : baseEnd_4401902 < baseStart_4401902 := by decide
  rcases family_descends (prefixWord ++ tailWord_4401902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4401989 : List Nat := [1, 3, 1, 1, 1, 2, 2, 1, 7, 1, 3]
def baseStart_4401989 : Nat := 118140960795 + 4401989 * 2 ^ 59
def prefixEnd_4401989 : Nat := 4983230072969 + 3 ^ 40 * 4401989 * 2
def baseEnd_4401989 : Nat := 2260336192804682931493127

theorem tailTrace_4401989 : CollatzResearch.WordTrace tailWord_4401989 prefixEnd_4401989 2260336192804682931493127 := by
  unfold tailWord_4401989
  simp only [CollatzResearch.WordTrace]
  refine ⟨160553728849353127712465021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107035819232902085141643347 160553728849353127712465021)
  ·
    refine ⟨60207648318507422892174383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160553728849353127712465021 60207648318507422892174383)
    ·
      refine ⟨90311472477761134338261575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60207648318507422892174383 90311472477761134338261575)
      ·
        refine ⟨135467208716641701507392363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90311472477761134338261575 135467208716641701507392363)
        ·
          refine ⟨203200813074962552261088545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135467208716641701507392363 203200813074962552261088545)
          ·
            refine ⟨152400609806221914195816409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 203200813074962552261088545 152400609806221914195816409)
            ·
              refine ⟨114300457354666435646862307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152400609806221914195816409 114300457354666435646862307)
              ·
                refine ⟨171450686031999653470293461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114300457354666435646862307 171450686031999653470293461)
                ·
                  refine ⟨4018375453874991878210003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 171450686031999653470293461 4018375453874991878210003)
                  ·
                    refine ⟨6027563180812487817315005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4018375453874991878210003 6027563180812487817315005)
                    ·
                      refine ⟨2260336192804682931493127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6027563180812487817315005 2260336192804682931493127)
                      ·
                        rfl

theorem cell23_4401989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 7, 1, 3].length) (baseStart_4401989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4401989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4401989 prefixEnd_4401989 := by exact prefixLift 4401989
  have htrace : WordTrace (prefixWord ++ tailWord_4401989) baseStart_4401989 baseEnd_4401989 := by
    simpa [prefixWord, tailWord_4401989, baseEnd_4401989] using wordTrace_append hprefix tailTrace_4401989
  have hstable : (prefixWord ++ tailWord_4401989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4401989).length < 2 ^ (prefixWord ++ tailWord_4401989).sum := by decide
  have hdescent : baseEnd_4401989 < baseStart_4401989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4401989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4402033 : List Nat := [1, 2, 2, 2, 1, 6, 1, 1, 2, 3, 2]
def baseStart_4402033 : Nat := 118140960795 + 4402033 * 2 ^ 59
def prefixEnd_4402033 : Nat := 4983230072969 + 3 ^ 40 * 4402033 * 2
def baseEnd_4402033 : Nat := 2260358785953480759342925

theorem tailTrace_4402033 : CollatzResearch.WordTrace tailWord_4402033 prefixEnd_4402033 2260358785953480759342925 := by
  unfold tailWord_4402033
  simp only [CollatzResearch.WordTrace]
  refine ⟨160555333661193723227066753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107036889107462482151377835 160555333661193723227066753)
  ·
    refine ⟨120416500245895292420300065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160555333661193723227066753 120416500245895292420300065)
    ·
      refine ⟨90312375184421469315225049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120416500245895292420300065 90312375184421469315225049)
      ·
        refine ⟨67734281388316101986418787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90312375184421469315225049 67734281388316101986418787)
        ·
          refine ⟨101601422082474152979628181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67734281388316101986418787 101601422082474152979628181)
          ·
            refine ⟨4762566660115975920920071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 101601422082474152979628181 4762566660115975920920071)
            ·
              refine ⟨7143849990173963881380107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4762566660115975920920071 7143849990173963881380107)
              ·
                refine ⟨10715774985260945822070161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7143849990173963881380107 10715774985260945822070161)
                ·
                  refine ⟨8036831238945709366552621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10715774985260945822070161 8036831238945709366552621)
                  ·
                    refine ⟨3013811714604641012457233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8036831238945709366552621 3013811714604641012457233)
                    ·
                      refine ⟨2260358785953480759342925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3013811714604641012457233 2260358785953480759342925)
                      ·
                        rfl

theorem cell23_4402033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 1, 2, 3, 2].length) (baseStart_4402033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4402033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4402033 prefixEnd_4402033 := by exact prefixLift 4402033
  have htrace : WordTrace (prefixWord ++ tailWord_4402033) baseStart_4402033 baseEnd_4402033 := by
    simpa [prefixWord, tailWord_4402033, baseEnd_4402033] using wordTrace_append hprefix tailTrace_4402033
  have hstable : (prefixWord ++ tailWord_4402033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4402033).length < 2 ^ (prefixWord ++ tailWord_4402033).sum := by decide
  have hdescent : baseEnd_4402033 < baseStart_4402033 := by decide
  rcases family_descends (prefixWord ++ tailWord_4402033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4402042 : List Nat := [3, 1, 1, 1, 1, 1, 3, 2, 3, 1, 6]
def baseStart_4402042 : Nat := 118140960795 + 4402042 * 2 ^ 59
def prefixEnd_4402042 : Nat := 4983230072969 + 3 ^ 40 * 4402042 * 2
def baseEnd_4402042 : Nat := 2260363407279371224130383

theorem tailTrace_4402042 : CollatzResearch.WordTrace tailWord_4402042 prefixEnd_4402042 2260363407279371224130383 := by
  unfold tailWord_4402042
  simp only [CollatzResearch.WordTrace]
  refine ⟨40138915479540279441036095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107037107945440745176096253 40138915479540279441036095)
  ·
    refine ⟨60208373219310419161554143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40138915479540279441036095 60208373219310419161554143)
    ·
      refine ⟨90312559828965628742331215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60208373219310419161554143 90312559828965628742331215)
      ·
        refine ⟨135468839743448443113496823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90312559828965628742331215 135468839743448443113496823)
        ·
          refine ⟨203203259615172664670245235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135468839743448443113496823 203203259615172664670245235)
          ·
            refine ⟨304804889422758997005367853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203203259615172664670245235 304804889422758997005367853)
            ·
              refine ⟨114301833533534623877012945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 304804889422758997005367853 114301833533534623877012945)
              ·
                refine ⟨85726375150150967907759709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114301833533534623877012945 85726375150150967907759709)
                ·
                  refine ⟨32147390681306612965409891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 85726375150150967907759709 32147390681306612965409891)
                  ·
                    refine ⟨48221086021959919448114837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32147390681306612965409891 48221086021959919448114837)
                    ·
                      refine ⟨2260363407279371224130383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48221086021959919448114837 2260363407279371224130383)
                      ·
                        rfl

theorem cell23_4402042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 3, 1, 6].length) (baseStart_4402042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4402042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4402042 prefixEnd_4402042 := by exact prefixLift 4402042
  have htrace : WordTrace (prefixWord ++ tailWord_4402042) baseStart_4402042 baseEnd_4402042 := by
    simpa [prefixWord, tailWord_4402042, baseEnd_4402042] using wordTrace_append hprefix tailTrace_4402042
  have hstable : (prefixWord ++ tailWord_4402042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4402042).length < 2 ^ (prefixWord ++ tailWord_4402042).sum := by decide
  have hdescent : baseEnd_4402042 < baseStart_4402042 := by decide
  rcases family_descends (prefixWord ++ tailWord_4402042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4402056 : List Nat := [2, 1, 3, 3, 2, 2, 1, 1, 4, 4]
def baseStart_4402056 : Nat := 118140960795 + 4402056 * 2 ^ 59
def prefixEnd_4402056 : Nat := 4983230072969 + 3 ^ 40 * 4402056 * 2
def baseEnd_4402056 : Nat := 753456865336178056451773

theorem tailTrace_4402056 : CollatzResearch.WordTrace tailWord_4402056 prefixEnd_4402056 753456865336178056451773 := by
  unfold tailWord_4402056
  simp only [CollatzResearch.WordTrace]
  refine ⟨80278086270055199077577011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107037448360073598770102681 80278086270055199077577011)
  ·
    refine ⟨120417129405082798616365517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80278086270055199077577011 120417129405082798616365517)
    ·
      refine ⟨45156423526906049481137069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120417129405082798616365517 45156423526906049481137069)
      ·
        refine ⟨16933658822589768555426401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45156423526906049481137069 16933658822589768555426401)
        ·
          refine ⟨12700244116942326416569801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16933658822589768555426401 12700244116942326416569801)
          ·
            refine ⟨9525183087706744812427351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12700244116942326416569801 9525183087706744812427351)
            ·
              refine ⟨14287774631560117218641027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9525183087706744812427351 14287774631560117218641027)
              ·
                refine ⟨21431661947340175827961541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14287774631560117218641027 21431661947340175827961541)
                ·
                  refine ⟨4018436615126282967742789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21431661947340175827961541 4018436615126282967742789)
                  ·
                    refine ⟨753456865336178056451773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4018436615126282967742789 753456865336178056451773)
                    ·
                      rfl

theorem cell23_4402056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 4, 4].length) (baseStart_4402056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4402056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4402056 prefixEnd_4402056 := by exact prefixLift 4402056
  have htrace : WordTrace (prefixWord ++ tailWord_4402056) baseStart_4402056 baseEnd_4402056 := by
    simpa [prefixWord, tailWord_4402056, baseEnd_4402056] using wordTrace_append hprefix tailTrace_4402056
  have hstable : (prefixWord ++ tailWord_4402056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4402056).length < 2 ^ (prefixWord ++ tailWord_4402056).sum := by decide
  have hdescent : baseEnd_4402056 < baseStart_4402056 := by decide
  rcases family_descends (prefixWord ++ tailWord_4402056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4402076 : List Nat := [2, 2, 3, 3, 2, 1, 1, 1, 1, 1, 6]
def baseStart_4402076 : Nat := 118140960795 + 4402076 * 2 ^ 59
def prefixEnd_4402076 : Nat := 4983230072969 + 3 ^ 40 * 4402076 * 2
def baseEnd_4402076 : Nat := 2260380865621624091105227

theorem tailTrace_4402076 : CollatzResearch.WordTrace tailWord_4402076 prefixEnd_4402076 2260380865621624091105227 := by
  unfold tailWord_4402076
  simp only [CollatzResearch.WordTrace]
  refine ⟨80278451000018970785441041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107037934666691961047254721 80278451000018970785441041)
  ·
    refine ⟨60208838250014228089080781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80278451000018970785441041 60208838250014228089080781)
    ·
      refine ⟨22578314343755335533405293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60208838250014228089080781 22578314343755335533405293)
      ·
        refine ⟨8466867878908250825026985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22578314343755335533405293 8466867878908250825026985)
        ·
          refine ⟨6350150909181188118770239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8466867878908250825026985 6350150909181188118770239)
          ·
            refine ⟨9525226363771782178155359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6350150909181188118770239 9525226363771782178155359)
            ·
              refine ⟨14287839545657673267233039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9525226363771782178155359 14287839545657673267233039)
              ·
                refine ⟨21431759318486509900849559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14287839545657673267233039 21431759318486509900849559)
                ·
                  refine ⟨32147638977729764851274339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21431759318486509900849559 32147638977729764851274339)
                  ·
                    refine ⟨48221458466594647276911509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32147638977729764851274339 48221458466594647276911509)
                    ·
                      refine ⟨2260380865621624091105227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48221458466594647276911509 2260380865621624091105227)
                      ·
                        rfl

theorem cell23_4402076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_4402076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4402076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4402076 prefixEnd_4402076 := by exact prefixLift 4402076
  have htrace : WordTrace (prefixWord ++ tailWord_4402076) baseStart_4402076 baseEnd_4402076 := by
    simpa [prefixWord, tailWord_4402076, baseEnd_4402076] using wordTrace_append hprefix tailTrace_4402076
  have hstable : (prefixWord ++ tailWord_4402076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4402076).length < 2 ^ (prefixWord ++ tailWord_4402076).sum := by decide
  have hdescent : baseEnd_4402076 < baseStart_4402076 := by decide
  rcases family_descends (prefixWord ++ tailWord_4402076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4402100 : List Nat := [2, 5, 2, 1, 1, 1, 2, 3, 1, 2, 3]
def baseStart_4402100 : Nat := 118140960795 + 4402100 * 2 ^ 59
def prefixEnd_4402100 : Nat := 4983230072969 + 3 ^ 40 * 4402100 * 2
def baseEnd_4402100 : Nat := 2260393189157331997205117

theorem tailTrace_4402100 : CollatzResearch.WordTrace tailWord_4402100 prefixEnd_4402100 2260393189157331997205117 := by
  unfold tailWord_4402100
  simp only [CollatzResearch.WordTrace]
  refine ⟨80278888675975496834877877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107038518234633995779837169 80278888675975496834877877)
  ·
    refine ⟨7526145813372702828269801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 80278888675975496834877877 7526145813372702828269801)
    ·
      refine ⟨5644609360029527121202351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7526145813372702828269801 5644609360029527121202351)
      ·
        refine ⟨8466914040044290681803527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5644609360029527121202351 8466914040044290681803527)
        ·
          refine ⟨12700371060066436022705291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8466914040044290681803527 12700371060066436022705291)
          ·
            refine ⟨19050556590099654034057937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12700371060066436022705291 19050556590099654034057937)
            ·
              refine ⟨14287917442574740525543453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19050556590099654034057937 14287917442574740525543453)
              ·
                refine ⟨5357969040965527697078795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14287917442574740525543453 5357969040965527697078795)
                ·
                  refine ⟨8036953561448291545618193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5357969040965527697078795 8036953561448291545618193)
                  ·
                    refine ⟨6027715171086218659213645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8036953561448291545618193 6027715171086218659213645)
                    ·
                      refine ⟨2260393189157331997205117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6027715171086218659213645 2260393189157331997205117)
                      ·
                        rfl

theorem cell23_4402100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_4402100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4402100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4402100 prefixEnd_4402100 := by exact prefixLift 4402100
  have htrace : WordTrace (prefixWord ++ tailWord_4402100) baseStart_4402100 baseEnd_4402100 := by
    simpa [prefixWord, tailWord_4402100, baseEnd_4402100] using wordTrace_append hprefix tailTrace_4402100
  have hstable : (prefixWord ++ tailWord_4402100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4402100).length < 2 ^ (prefixWord ++ tailWord_4402100).sum := by decide
  have hdescent : baseEnd_4402100 < baseStart_4402100 := by decide
  rcases family_descends (prefixWord ++ tailWord_4402100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4402130 : List Nat := [3, 2, 2, 3, 1, 2, 1, 3, 2, 1, 3]
def baseStart_4402130 : Nat := 118140960795 + 4402130 * 2 ^ 59
def prefixEnd_4402130 : Nat := 4983230072969 + 3 ^ 40 * 4402130 * 2
def baseEnd_4402130 : Nat := 2260408593576966879829979

theorem tailTrace_4402130 : CollatzResearch.WordTrace tailWord_4402130 prefixEnd_4402130 2260408593576966879829979 := by
  unfold tailWord_4402130
  simp only [CollatzResearch.WordTrace]
  refine ⟨40139717885460577198336961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107039247694561539195565229 40139717885460577198336961)
  ·
    refine ⟨30104788414095432898752721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40139717885460577198336961 30104788414095432898752721)
    ·
      refine ⟨22578591310571574674064541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30104788414095432898752721 22578591310571574674064541)
      ·
        refine ⟨8466971741464340502774203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22578591310571574674064541 8466971741464340502774203)
        ·
          refine ⟨12700457612196510754161305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8466971741464340502774203 12700457612196510754161305)
          ·
            refine ⟨9525343209147383065620979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12700457612196510754161305 9525343209147383065620979)
            ·
              refine ⟨14288014813721074598431469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9525343209147383065620979 14288014813721074598431469)
              ·
                refine ⟨5358005555145402974411801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14288014813721074598431469 5358005555145402974411801)
                ·
                  refine ⟨4018504166359052230808851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5358005555145402974411801 4018504166359052230808851)
                  ·
                    refine ⟨6027756249538578346213277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4018504166359052230808851 6027756249538578346213277)
                    ·
                      refine ⟨2260408593576966879829979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6027756249538578346213277 2260408593576966879829979)
                      ·
                        rfl

theorem cell23_4402130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_4402130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4402130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4402130 prefixEnd_4402130 := by exact prefixLift 4402130
  have htrace : WordTrace (prefixWord ++ tailWord_4402130) baseStart_4402130 baseEnd_4402130 := by
    simpa [prefixWord, tailWord_4402130, baseEnd_4402130] using wordTrace_append hprefix tailTrace_4402130
  have hstable : (prefixWord ++ tailWord_4402130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4402130).length < 2 ^ (prefixWord ++ tailWord_4402130).sum := by decide
  have hdescent : baseEnd_4402130 < baseStart_4402130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4402130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4402186 : List Nat := [3, 1, 2, 2, 3, 1, 1, 1, 1, 5, 3]
def baseStart_4402186 : Nat := 118140960795 + 4402186 * 2 ^ 59
def prefixEnd_4402186 : Nat := 4983230072969 + 3 ^ 40 * 4402186 * 2
def baseEnd_4402186 : Nat := 2260437348493618660729721

theorem tailTrace_4402186 : CollatzResearch.WordTrace tailWord_4402186 prefixEnd_4402186 2260437348493618660729721 := by
  unfold tailWord_4402186
  simp only [CollatzResearch.WordTrace]
  refine ⟨40140228507409857589346603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107040609353092953571590941 40140228507409857589346603)
  ·
    refine ⟨60210342761114786384019905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40140228507409857589346603 60210342761114786384019905)
    ·
      refine ⟨45157757070836089788014929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60210342761114786384019905 45157757070836089788014929)
      ·
        refine ⟨33868317803127067341011197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45157757070836089788014929 33868317803127067341011197)
        ·
          refine ⟨12700619176172650252879199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33868317803127067341011197 12700619176172650252879199)
          ·
            refine ⟨19050928764258975379318799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12700619176172650252879199 19050928764258975379318799)
            ·
              refine ⟨28576393146388463068978199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19050928764258975379318799 28576393146388463068978199)
              ·
                refine ⟨42864589719582694603467299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28576393146388463068978199 42864589719582694603467299)
                ·
                  refine ⟨64296884579374041905200949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42864589719582694603467299 64296884579374041905200949)
                  ·
                    refine ⟨6027832929316316428612589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 64296884579374041905200949 6027832929316316428612589)
                    ·
                      refine ⟨2260437348493618660729721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6027832929316316428612589 2260437348493618660729721)
                      ·
                        rfl

theorem cell23_4402186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 1, 5, 3].length) (baseStart_4402186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4402186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4402186 prefixEnd_4402186 := by exact prefixLift 4402186
  have htrace : WordTrace (prefixWord ++ tailWord_4402186) baseStart_4402186 baseEnd_4402186 := by
    simpa [prefixWord, tailWord_4402186, baseEnd_4402186] using wordTrace_append hprefix tailTrace_4402186
  have hstable : (prefixWord ++ tailWord_4402186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4402186).length < 2 ^ (prefixWord ++ tailWord_4402186).sum := by decide
  have hdescent : baseEnd_4402186 < baseStart_4402186 := by decide
  rcases family_descends (prefixWord ++ tailWord_4402186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4402226 : List Nat := [3, 2, 1, 1, 2, 2, 2, 1, 4, 1, 4]
def baseStart_4402226 : Nat := 118140960795 + 4402226 * 2 ^ 59
def prefixEnd_4402226 : Nat := 4983230072969 + 3 ^ 40 * 4402226 * 2
def baseEnd_4402226 : Nat := 2260457887719798504229537

theorem tailTrace_4402226 : CollatzResearch.WordTrace tailWord_4402226 prefixEnd_4402226 2260457887719798504229537 := by
  unfold tailWord_4402226
  simp only [CollatzResearch.WordTrace]
  refine ⟨40140593237373629297210633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107041581966329678125895021 40140593237373629297210633)
  ·
    refine ⟨30105444928030221972907975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40140593237373629297210633 30105444928030221972907975)
    ·
      refine ⟨45158167392045332959361963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30105444928030221972907975 45158167392045332959361963)
      ·
        refine ⟨67737251088067999439042945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45158167392045332959361963 67737251088067999439042945)
        ·
          refine ⟨50802938316050999579282209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67737251088067999439042945 50802938316050999579282209)
          ·
            refine ⟨38102203737038249684461657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50802938316050999579282209 38102203737038249684461657)
            ·
              refine ⟨28576652802778687263346243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38102203737038249684461657 28576652802778687263346243)
              ·
                refine ⟨42864979204168030895019365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28576652802778687263346243 42864979204168030895019365)
                ·
                  refine ⟨8037183600781505792816131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42864979204168030895019365 8037183600781505792816131)
                  ·
                    refine ⟨12055775401172258689224197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8037183600781505792816131 12055775401172258689224197)
                    ·
                      refine ⟨2260457887719798504229537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12055775401172258689224197 2260457887719798504229537)
                      ·
                        rfl

theorem cell23_4402226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 4, 1, 4].length) (baseStart_4402226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4402226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4402226 prefixEnd_4402226 := by exact prefixLift 4402226
  have htrace : WordTrace (prefixWord ++ tailWord_4402226) baseStart_4402226 baseEnd_4402226 := by
    simpa [prefixWord, tailWord_4402226, baseEnd_4402226] using wordTrace_append hprefix tailTrace_4402226
  have hstable : (prefixWord ++ tailWord_4402226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4402226).length < 2 ^ (prefixWord ++ tailWord_4402226).sum := by decide
  have hdescent : baseEnd_4402226 < baseStart_4402226 := by decide
  rcases family_descends (prefixWord ++ tailWord_4402226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4402239 : List Nat := [1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 6]
def baseStart_4402239 : Nat := 118140960795 + 4402239 * 2 ^ 59
def prefixEnd_4402239 : Nat := 4983230072969 + 3 ^ 40 * 4402239 * 2
def baseEnd_4402239 : Nat := 2260464562968306953366977

theorem tailTrace_4402239 : CollatzResearch.WordTrace tailWord_4402239 prefixEnd_4402239 2260464562968306953366977 := by
  unfold tailWord_4402239
  simp only [CollatzResearch.WordTrace]
  refine ⟨160562847098447420409065771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107041898065631613606043847 160562847098447420409065771)
  ·
    refine ⟨240844270647671130613598657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160562847098447420409065771 240844270647671130613598657)
    ·
      refine ⟨180633202985753347960198993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 240844270647671130613598657 180633202985753347960198993)
      ·
        refine ⟨135474902239315010970149245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180633202985753347960198993 135474902239315010970149245)
        ·
          refine ⟨50803088339743129113805967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135474902239315010970149245 50803088339743129113805967)
          ·
            refine ⟨76204632509614693670708951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50803088339743129113805967 76204632509614693670708951)
            ·
              refine ⟨114306948764422040506063427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76204632509614693670708951 114306948764422040506063427)
              ·
                refine ⟨171460423146633060759095141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114306948764422040506063427 171460423146633060759095141)
                ·
                  refine ⟨32148829339993698892330339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 171460423146633060759095141 32148829339993698892330339)
                  ·
                    refine ⟨48223244009990548338495509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32148829339993698892330339 48223244009990548338495509)
                    ·
                      refine ⟨2260464562968306953366977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48223244009990548338495509 2260464562968306953366977)
                      ·
                        rfl

theorem cell23_4402239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 6].length) (baseStart_4402239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4402239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4402239 prefixEnd_4402239 := by exact prefixLift 4402239
  have htrace : WordTrace (prefixWord ++ tailWord_4402239) baseStart_4402239 baseEnd_4402239 := by
    simpa [prefixWord, tailWord_4402239, baseEnd_4402239] using wordTrace_append hprefix tailTrace_4402239
  have hstable : (prefixWord ++ tailWord_4402239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4402239).length < 2 ^ (prefixWord ++ tailWord_4402239).sum := by decide
  have hdescent : baseEnd_4402239 < baseStart_4402239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4402239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4402313 : List Nat := [1, 2, 1, 1, 4, 3, 3, 2, 1, 5]
def baseStart_4402313 : Nat := 118140960795 + 4402313 * 2 ^ 59
def prefixEnd_4402313 : Nat := 4983230072969 + 3 ^ 40 * 4402313 * 2
def baseEnd_4402313 : Nat := 753500853512246554613879

theorem tailTrace_4402313 : CollatzResearch.WordTrace tailWord_4402313 prefixEnd_4402313 753500853512246554613879 := by
  unfold tailWord_4402313
  simp only [CollatzResearch.WordTrace]
  refine ⟨160565546100179331047259593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107043697400119554031506395 160565546100179331047259593)
  ·
    refine ⟨120424159575134498285444695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160565546100179331047259593 120424159575134498285444695)
    ·
      refine ⟨180636239362701747428167043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120424159575134498285444695 180636239362701747428167043)
      ·
        refine ⟨270954359044052621142250565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180636239362701747428167043 270954359044052621142250565)
        ·
          refine ⟨50803942320759866464171981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 270954359044052621142250565 50803942320759866464171981)
          ·
            refine ⟨19051478370284949924064493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50803942320759866464171981 19051478370284949924064493)
            ·
              refine ⟨7144304388856856221524185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19051478370284949924064493 7144304388856856221524185)
              ·
                refine ⟨5358228291642642166143139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7144304388856856221524185 5358228291642642166143139)
                ·
                  refine ⟨8037342437463963249214709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5358228291642642166143139 8037342437463963249214709)
                  ·
                    refine ⟨753500853512246554613879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8037342437463963249214709 753500853512246554613879)
                    ·
                      rfl

theorem cell23_4402313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 2, 1, 5].length) (baseStart_4402313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4402313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4402313 prefixEnd_4402313 := by exact prefixLift 4402313
  have htrace : WordTrace (prefixWord ++ tailWord_4402313) baseStart_4402313 baseEnd_4402313 := by
    simpa [prefixWord, tailWord_4402313, baseEnd_4402313] using wordTrace_append hprefix tailTrace_4402313
  have hstable : (prefixWord ++ tailWord_4402313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4402313).length < 2 ^ (prefixWord ++ tailWord_4402313).sum := by decide
  have hdescent : baseEnd_4402313 < baseStart_4402313 := by decide
  rcases family_descends (prefixWord ++ tailWord_4402313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4402381 : List Nat := [1, 6, 2, 2, 1, 2, 2, 1, 1, 5]
def baseStart_4402381 : Nat := 118140960795 + 4402381 * 2 ^ 59
def prefixEnd_4402381 : Nat := 4983230072969 + 3 ^ 40 * 4402381 * 2
def baseEnd_4402381 : Nat := 753512492407081799263775

theorem tailTrace_4402381 : CollatzResearch.WordTrace tailWord_4402381 prefixEnd_4402381 753512492407081799263775 := by
  unfold tailWord_4402381
  simp only [CollatzResearch.WordTrace]
  refine ⟨160568026263932978660734997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107045350842621985773823331 160568026263932978660734997)
  ·
    refine ⟨7526626231121858374721953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 160568026263932978660734997 7526626231121858374721953)
    ·
      refine ⟨5644969673341393781041465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7526626231121858374721953 5644969673341393781041465)
      ·
        refine ⟨4233727255006045335781099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5644969673341393781041465 4233727255006045335781099)
        ·
          refine ⟨6350590882509068003671649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4233727255006045335781099 6350590882509068003671649)
          ·
            refine ⟨4762943161881801002753737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6350590882509068003671649 4762943161881801002753737)
            ·
              refine ⟨3572207371411350752065303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4762943161881801002753737 3572207371411350752065303)
              ·
                refine ⟨5358311057117026128097955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3572207371411350752065303 5358311057117026128097955)
                ·
                  refine ⟨8037466585675539192146933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5358311057117026128097955 8037466585675539192146933)
                  ·
                    refine ⟨753512492407081799263775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8037466585675539192146933 753512492407081799263775)
                    ·
                      rfl

theorem cell23_4402381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_4402381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4402381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4402381 prefixEnd_4402381 := by exact prefixLift 4402381
  have htrace : WordTrace (prefixWord ++ tailWord_4402381) baseStart_4402381 baseEnd_4402381 := by
    simpa [prefixWord, tailWord_4402381, baseEnd_4402381] using wordTrace_append hprefix tailTrace_4402381
  have hstable : (prefixWord ++ tailWord_4402381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4402381).length < 2 ^ (prefixWord ++ tailWord_4402381).sum := by decide
  have hdescent : baseEnd_4402381 < baseStart_4402381 := by decide
  rcases family_descends (prefixWord ++ tailWord_4402381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4402390 : List Nat := [5, 2, 1, 2, 2, 1, 10]
def baseStart_4402390 : Nat := 118140960795 + 4402390 * 2 ^ 59
def prefixEnd_4402390 : Nat := 4983230072969 + 3 ^ 40 * 4402390 * 2
def baseEnd_4402390 : Nat := 27907927142557232871343

theorem tailTrace_4402390 : CollatzResearch.WordTrace tailWord_4402390 prefixEnd_4402390 27907927142557232871343 := by
  unfold tailWord_4402390
  simp only [CollatzResearch.WordTrace]
  refine ⟨10035522157556273324863289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 107045569680600248798541749 10035522157556273324863289)
  ·
    refine ⟨7526641618167204993647467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10035522157556273324863289 7526641618167204993647467)
    ·
      refine ⟨11289962427250807490471201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7526641618167204993647467 11289962427250807490471201)
      ·
        refine ⟨8467471820438105617853401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11289962427250807490471201 8467471820438105617853401)
        ·
          refine ⟨6350603865328579213390051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8467471820438105617853401 6350603865328579213390051)
          ·
            refine ⟨9525905797992868820085077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6350603865328579213390051 9525905797992868820085077)
            ·
              refine ⟨27907927142557232871343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9525905797992868820085077 27907927142557232871343)
              ·
                rfl

theorem cell23_4402390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 10].length) (baseStart_4402390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4402390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4402390 prefixEnd_4402390 := by exact prefixLift 4402390
  have htrace : WordTrace (prefixWord ++ tailWord_4402390) baseStart_4402390 baseEnd_4402390 := by
    simpa [prefixWord, tailWord_4402390, baseEnd_4402390] using wordTrace_append hprefix tailTrace_4402390
  have hstable : (prefixWord ++ tailWord_4402390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4402390).length < 2 ^ (prefixWord ++ tailWord_4402390).sum := by decide
  have hdescent : baseEnd_4402390 < baseStart_4402390 := by decide
  rcases family_descends (prefixWord ++ tailWord_4402390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4402400 : List Nat := [2, 1, 1, 3, 1, 5, 1, 1, 4, 1, 3]
def baseStart_4402400 : Nat := 118140960795 + 4402400 * 2 ^ 59
def prefixEnd_4402400 : Nat := 4983230072969 + 3 ^ 40 * 4402400 * 2
def baseEnd_4402400 : Nat := 2260547233353680823453737

theorem tailTrace_4402400 : CollatzResearch.WordTrace tailWord_4402400 prefixEnd_4402400 2260547233353680823453737 := by
  unfold tailWord_4402400
  simp only [CollatzResearch.WordTrace]
  refine ⟨80284359625432072452838327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107045812833909429937117769 80284359625432072452838327)
  ·
    refine ⟨120426539438148108679257491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80284359625432072452838327 120426539438148108679257491)
    ·
      refine ⟨180639809157222163018886237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120426539438148108679257491 180639809157222163018886237)
      ·
        refine ⟨67739928433958311132082339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 180639809157222163018886237 67739928433958311132082339)
        ·
          refine ⟨101609892650937466698123509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67739928433958311132082339 101609892650937466698123509)
          ·
            refine ⟨9525927436025387502949079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 101609892650937466698123509 9525927436025387502949079)
            ·
              refine ⟨14288891154038081254423619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9525927436025387502949079 14288891154038081254423619)
              ·
                refine ⟨21433336731057121881635429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14288891154038081254423619 21433336731057121881635429)
                ·
                  refine ⟨4018750637073210352806643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21433336731057121881635429 4018750637073210352806643)
                  ·
                    refine ⟨6028125955609815529209965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4018750637073210352806643 6028125955609815529209965)
                    ·
                      refine ⟨2260547233353680823453737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6028125955609815529209965 2260547233353680823453737)
                      ·
                        rfl

theorem cell23_4402400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 4, 1, 3].length) (baseStart_4402400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4402400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4402400 prefixEnd_4402400 := by exact prefixLift 4402400
  have htrace : WordTrace (prefixWord ++ tailWord_4402400) baseStart_4402400 baseEnd_4402400 := by
    simpa [prefixWord, tailWord_4402400, baseEnd_4402400] using wordTrace_append hprefix tailTrace_4402400
  have hstable : (prefixWord ++ tailWord_4402400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4402400).length < 2 ^ (prefixWord ++ tailWord_4402400).sum := by decide
  have hdescent : baseEnd_4402400 < baseStart_4402400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4402400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4402443 : List Nat := [1, 1, 1, 1, 5, 4, 1, 1, 2, 1, 5]
def baseStart_4402443 : Nat := 118140960795 + 4402443 * 2 ^ 59
def prefixEnd_4402443 : Nat := 4983230072969 + 3 ^ 40 * 4402443 * 2
def baseEnd_4402443 : Nat := 2260569313021824155216039

theorem tailTrace_4402443 : CollatzResearch.WordTrace tailWord_4402443 prefixEnd_4402443 2260569313021824155216039 := by
  unfold tailWord_4402443
  simp only [CollatzResearch.WordTrace]
  refine ⟨160570287589708363249491983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107046858393138908832994655 160570287589708363249491983)
  ·
    refine ⟨240855431384562544874237975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160570287589708363249491983 240855431384562544874237975)
    ·
      refine ⟨361283147076843817311356963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240855431384562544874237975 361283147076843817311356963)
      ·
        refine ⟨541924720615265725967035445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 361283147076843817311356963 541924720615265725967035445)
        ·
          refine ⟨50805442557681161809409573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 541924720615265725967035445 50805442557681161809409573)
          ·
            refine ⟨9526020479565217839264295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50805442557681161809409573 9526020479565217839264295)
            ·
              refine ⟨14289030719347826758896443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9526020479565217839264295 14289030719347826758896443)
              ·
                refine ⟨21433546079021740138344665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14289030719347826758896443 21433546079021740138344665)
                ·
                  refine ⟨16075159559266305103758499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21433546079021740138344665 16075159559266305103758499)
                  ·
                    refine ⟨24112739338899457655637749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16075159559266305103758499 24112739338899457655637749)
                    ·
                      refine ⟨2260569313021824155216039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24112739338899457655637749 2260569313021824155216039)
                      ·
                        rfl

theorem cell23_4402443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 2, 1, 5].length) (baseStart_4402443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4402443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4402443 prefixEnd_4402443 := by exact prefixLift 4402443
  have htrace : WordTrace (prefixWord ++ tailWord_4402443) baseStart_4402443 baseEnd_4402443 := by
    simpa [prefixWord, tailWord_4402443, baseEnd_4402443] using wordTrace_append hprefix tailTrace_4402443
  have hstable : (prefixWord ++ tailWord_4402443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4402443).length < 2 ^ (prefixWord ++ tailWord_4402443).sum := by decide
  have hdescent : baseEnd_4402443 < baseStart_4402443 := by decide
  rcases family_descends (prefixWord ++ tailWord_4402443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4402503 : List Nat := [1, 1, 4, 1, 2, 3, 1, 2, 1, 2, 5]
def baseStart_4402503 : Nat := 118140960795 + 4402503 * 2 ^ 59
def prefixEnd_4402503 : Nat := 4983230072969 + 3 ^ 40 * 4402503 * 2
def baseEnd_4402503 : Nat := 2260600121861093920465763

theorem tailTrace_4402503 : CollatzResearch.WordTrace tailWord_4402503 prefixEnd_4402503 2260600121861093920465763 := by
  unfold tailWord_4402503
  simp only [CollatzResearch.WordTrace]
  refine ⟨160572475969490993496676163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107048317312993995664450775 160572475969490993496676163)
  ·
    refine ⟨240858713954236490245014245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160572475969490993496676163 240858713954236490245014245)
    ·
      refine ⟨45161008866419341920940171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 240858713954236490245014245 45161008866419341920940171)
      ·
        refine ⟨67741513299629012881410257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45161008866419341920940171 67741513299629012881410257)
        ·
          refine ⟨50806134974721759661057693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67741513299629012881410257 50806134974721759661057693)
          ·
            refine ⟨19052300615520659872896635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50806134974721759661057693 19052300615520659872896635)
            ·
              refine ⟨28578450923280989809344953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19052300615520659872896635 28578450923280989809344953)
              ·
                refine ⟨21433838192460742357008715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28578450923280989809344953 21433838192460742357008715)
                ·
                  refine ⟨32150757288691113535513073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21433838192460742357008715 32150757288691113535513073)
                  ·
                    refine ⟨24113067966518335151634805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32150757288691113535513073 24113067966518335151634805)
                    ·
                      refine ⟨2260600121861093920465763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24113067966518335151634805 2260600121861093920465763)
                      ·
                        rfl

theorem cell23_4402503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 2, 5].length) (baseStart_4402503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4402503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4402503 prefixEnd_4402503 := by exact prefixLift 4402503
  have htrace : WordTrace (prefixWord ++ tailWord_4402503) baseStart_4402503 baseEnd_4402503 := by
    simpa [prefixWord, tailWord_4402503, baseEnd_4402503] using wordTrace_append hprefix tailTrace_4402503
  have hstable : (prefixWord ++ tailWord_4402503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4402503).length < 2 ^ (prefixWord ++ tailWord_4402503).sum := by decide
  have hdescent : baseEnd_4402503 < baseStart_4402503 := by decide
  rcases family_descends (prefixWord ++ tailWord_4402503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4402530 : List Nat := [3, 3, 2, 1, 1, 1, 2, 2, 1, 3, 4]
def baseStart_4402530 : Nat := 118140960795 + 4402530 * 2 ^ 59
def prefixEnd_4402530 : Nat := 4983230072969 + 3 ^ 40 * 4402530 * 2
def baseEnd_4402530 : Nat := 2260613985838765314828139

theorem tailTrace_4402530 : CollatzResearch.WordTrace tailWord_4402530 prefixEnd_4402530 2260613985838765314828139 := by
  unfold tailWord_4402530
  simp only [CollatzResearch.WordTrace]
  refine ⟨40143365185098294276977261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107048973826928784738606029 40143365185098294276977261)
  ·
    refine ⟨15053761944411860353866473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40143365185098294276977261 15053761944411860353866473)
    ·
      refine ⟨11290321458308895265399855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15053761944411860353866473 11290321458308895265399855)
      ·
        refine ⟨16935482187463342898099783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11290321458308895265399855 16935482187463342898099783)
        ·
          refine ⟨25403223281195014347149675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16935482187463342898099783 25403223281195014347149675)
          ·
            refine ⟨38104834921792521520724513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25403223281195014347149675 38104834921792521520724513)
            ·
              refine ⟨28578626191344391140543385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38104834921792521520724513 28578626191344391140543385)
              ·
                refine ⟨21433969643508293355407539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28578626191344391140543385 21433969643508293355407539)
                ·
                  refine ⟨32150954465262440033111309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21433969643508293355407539 32150954465262440033111309)
                  ·
                    refine ⟨12056607924473415012416741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32150954465262440033111309 12056607924473415012416741)
                    ·
                      refine ⟨2260613985838765314828139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12056607924473415012416741 2260613985838765314828139)
                      ·
                        rfl

theorem cell23_4402530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_4402530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4402530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4402530 prefixEnd_4402530 := by exact prefixLift 4402530
  have htrace : WordTrace (prefixWord ++ tailWord_4402530) baseStart_4402530 baseEnd_4402530 := by
    simpa [prefixWord, tailWord_4402530, baseEnd_4402530] using wordTrace_append hprefix tailTrace_4402530
  have hstable : (prefixWord ++ tailWord_4402530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4402530).length < 2 ^ (prefixWord ++ tailWord_4402530).sum := by decide
  have hdescent : baseEnd_4402530 < baseStart_4402530 := by decide
  rcases family_descends (prefixWord ++ tailWord_4402530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4402540 : List Nat := [2, 2, 1, 1, 5, 1, 1, 1, 5, 4]
def baseStart_4402540 : Nat := 118140960795 + 4402540 * 2 ^ 59
def prefixEnd_4402540 : Nat := 4983230072969 + 3 ^ 40 * 4402540 * 2
def baseEnd_4402540 : Nat := 753539706881770091901031

theorem tailTrace_4402540 : CollatzResearch.WordTrace tailWord_4402540 prefixEnd_4402540 753539706881770091901031 := by
  unfold tailWord_4402540
  simp only [CollatzResearch.WordTrace]
  refine ⟨80286912735178474407886537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107049216980237965877182049 80286912735178474407886537)
  ·
    refine ⟨60215184551383855805914903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80286912735178474407886537 60215184551383855805914903)
    ·
      refine ⟨90322776827075783708872355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60215184551383855805914903 90322776827075783708872355)
      ·
        refine ⟨135484165240613675563308533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90322776827075783708872355 135484165240613675563308533)
        ·
          refine ⟨12701640491307532084060175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 135484165240613675563308533 12701640491307532084060175)
          ·
            refine ⟨19052460736961298126090263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12701640491307532084060175 19052460736961298126090263)
            ·
              refine ⟨28578691105441947189135395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19052460736961298126090263 28578691105441947189135395)
              ·
                refine ⟨42868036658162920783703093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28578691105441947189135395 42868036658162920783703093)
                ·
                  refine ⟨4018878436702773823472165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42868036658162920783703093 4018878436702773823472165)
                  ·
                    refine ⟨753539706881770091901031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4018878436702773823472165 753539706881770091901031)
                    ·
                      rfl

theorem cell23_4402540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 4].length) (baseStart_4402540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4402540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4402540 prefixEnd_4402540 := by exact prefixLift 4402540
  have htrace : WordTrace (prefixWord ++ tailWord_4402540) baseStart_4402540 baseEnd_4402540 := by
    simpa [prefixWord, tailWord_4402540, baseEnd_4402540] using wordTrace_append hprefix tailTrace_4402540
  have hstable : (prefixWord ++ tailWord_4402540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4402540).length < 2 ^ (prefixWord ++ tailWord_4402540).sum := by decide
  have hdescent : baseEnd_4402540 < baseStart_4402540 := by decide
  rcases family_descends (prefixWord ++ tailWord_4402540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4402574 : List Nat := [4, 1, 1, 4, 2, 1, 2, 1, 3, 4]
def baseStart_4402574 : Nat := 118140960795 + 4402574 * 2 ^ 59
def prefixEnd_4402574 : Nat := 4983230072969 + 3 ^ 40 * 4402574 * 2
def baseEnd_4402574 : Nat := 753545526329187714225979

theorem tailTrace_4402574 : CollatzResearch.WordTrace tailWord_4402574 prefixEnd_4402574 753545526329187714225979 := by
  unfold tailWord_4402574
  simp only [CollatzResearch.WordTrace]
  refine ⟨20071883194029221577813847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107050043701489181748340517 20071883194029221577813847)
  ·
    refine ⟨30107824791043832366720771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20071883194029221577813847 30107824791043832366720771)
    ·
      refine ⟨45161737186565748550081157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30107824791043832366720771 45161737186565748550081157)
      ·
        refine ⟨8467825722481077853140217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45161737186565748550081157 8467825722481077853140217)
        ·
          refine ⟨6350869291860808389855163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8467825722481077853140217 6350869291860808389855163)
          ·
            refine ⟨9526303937791212584782745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6350869291860808389855163 9526303937791212584782745)
            ·
              refine ⟨7144727953343409438587059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9526303937791212584782745 7144727953343409438587059)
              ·
                refine ⟨10717091930015114157880589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7144727953343409438587059 10717091930015114157880589)
                ·
                  refine ⟨4018909473755667809205221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10717091930015114157880589 4018909473755667809205221)
                  ·
                    refine ⟨753545526329187714225979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4018909473755667809205221 753545526329187714225979)
                    ·
                      rfl

theorem cell23_4402574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 1, 3, 4].length) (baseStart_4402574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4402574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4402574 prefixEnd_4402574 := by exact prefixLift 4402574
  have htrace : WordTrace (prefixWord ++ tailWord_4402574) baseStart_4402574 baseEnd_4402574 := by
    simpa [prefixWord, tailWord_4402574, baseEnd_4402574] using wordTrace_append hprefix tailTrace_4402574
  have hstable : (prefixWord ++ tailWord_4402574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4402574).length < 2 ^ (prefixWord ++ tailWord_4402574).sum := by decide
  have hdescent : baseEnd_4402574 < baseStart_4402574 := by decide
  rcases family_descends (prefixWord ++ tailWord_4402574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4402631 : List Nat := [1, 1, 4, 1, 1, 3, 5, 2, 1, 1, 3]
def baseStart_4402631 : Nat := 118140960795 + 4402631 * 2 ^ 59
def prefixEnd_4402631 : Nat := 4983230072969 + 3 ^ 40 * 4402631 * 2
def baseEnd_4402631 : Nat := 2260665847384869419665175

theorem tailTrace_4402631 : CollatzResearch.WordTrace tailWord_4402631 prefixEnd_4402631 2260665847384869419665175 := by
  unfold tailWord_4402631
  simp only [CollatzResearch.WordTrace]
  refine ⟨160577144513027271357335747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107051429675351514238223831 160577144513027271357335747)
  ·
    refine ⟨240865716769540907036003621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160577144513027271357335747 240865716769540907036003621)
    ·
      refine ⟨45162321894288920069250679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 240865716769540907036003621 45162321894288920069250679)
      ·
        refine ⟨67743482841433380103876019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45162321894288920069250679 67743482841433380103876019)
        ·
          refine ⟨101615224262150070155814029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67743482841433380103876019 101615224262150070155814029)
          ·
            refine ⟨38105709098306276308430261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101615224262150070155814029 38105709098306276308430261)
            ·
              refine ⟨3572410227966213403915337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38105709098306276308430261 3572410227966213403915337)
              ·
                refine ⟨2679307670974660052936503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3572410227966213403915337 2679307670974660052936503)
                ·
                  refine ⟨4018961506461990079404755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2679307670974660052936503 4018961506461990079404755)
                  ·
                    refine ⟨6028442259692985119107133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4018961506461990079404755 6028442259692985119107133)
                    ·
                      refine ⟨2260665847384869419665175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6028442259692985119107133 2260665847384869419665175)
                      ·
                        rfl

theorem cell23_4402631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 5, 2, 1, 1, 3].length) (baseStart_4402631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4402631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4402631 prefixEnd_4402631 := by exact prefixLift 4402631
  have htrace : WordTrace (prefixWord ++ tailWord_4402631) baseStart_4402631 baseEnd_4402631 := by
    simpa [prefixWord, tailWord_4402631, baseEnd_4402631] using wordTrace_append hprefix tailTrace_4402631
  have hstable : (prefixWord ++ tailWord_4402631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4402631).length < 2 ^ (prefixWord ++ tailWord_4402631).sum := by decide
  have hdescent : baseEnd_4402631 < baseStart_4402631 := by decide
  rcases family_descends (prefixWord ++ tailWord_4402631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4402640 : List Nat := [2, 1, 1, 1, 1, 2, 2, 3, 5, 2, 3]
def baseStart_4402640 : Nat := 118140960795 + 4402640 * 2 ^ 59
def prefixEnd_4402640 : Nat := 4983230072969 + 3 ^ 40 * 4402640 * 2
def baseEnd_4402640 : Nat := 2260670468710759884452633

theorem tailTrace_4402640 : CollatzResearch.WordTrace tailWord_4402640 prefixEnd_4402640 2260670468710759884452633 := by
  unfold tailWord_4402640
  simp only [CollatzResearch.WordTrace]
  refine ⟨80288736384997332947206687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107051648513329777262942249 80288736384997332947206687)
  ·
    refine ⟨120433104577495999420810031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80288736384997332947206687 120433104577495999420810031)
    ·
      refine ⟨180649656866243999131215047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120433104577495999420810031 180649656866243999131215047)
      ·
        refine ⟨270974485299365998696822571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180649656866243999131215047 270974485299365998696822571)
        ·
          refine ⟨406461727949048998045233857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270974485299365998696822571 406461727949048998045233857)
          ·
            refine ⟨304846295961786748533925393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 406461727949048998045233857 304846295961786748533925393)
            ·
              refine ⟨228634721971340061400444045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 304846295961786748533925393 228634721971340061400444045)
              ·
                refine ⟨85738020739252523025166517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 228634721971340061400444045 85738020739252523025166517)
                ·
                  refine ⟨8037939444304924033609361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 85738020739252523025166517 8037939444304924033609361)
                  ·
                    refine ⟨6028454583228693025207021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8037939444304924033609361 6028454583228693025207021)
                    ·
                      refine ⟨2260670468710759884452633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6028454583228693025207021 2260670468710759884452633)
                      ·
                        rfl

theorem cell23_4402640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 5, 2, 3].length) (baseStart_4402640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4402640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4402640 prefixEnd_4402640 := by exact prefixLift 4402640
  have htrace : WordTrace (prefixWord ++ tailWord_4402640) baseStart_4402640 baseEnd_4402640 := by
    simpa [prefixWord, tailWord_4402640, baseEnd_4402640] using wordTrace_append hprefix tailTrace_4402640
  have hstable : (prefixWord ++ tailWord_4402640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4402640).length < 2 ^ (prefixWord ++ tailWord_4402640).sum := by decide
  have hdescent : baseEnd_4402640 < baseStart_4402640 := by decide
  rcases family_descends (prefixWord ++ tailWord_4402640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4402650 : List Nat := [3, 1, 1, 2, 3, 2, 2, 1, 1, 1, 6]
def baseStart_4402650 : Nat := 118140960795 + 4402650 * 2 ^ 59
def prefixEnd_4402650 : Nat := 4983230072969 + 3 ^ 40 * 4402650 * 2
def baseEnd_4402650 : Nat := 2260675603517304845327587

theorem tailTrace_4402650 : CollatzResearch.WordTrace tailWord_4402650 prefixEnd_4402650 2260675603517304845327587 := by
  unfold tailWord_4402650
  simp only [CollatzResearch.WordTrace]
  refine ⟨40144459374989609400569351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107051891666638958401518269 40144459374989609400569351)
  ·
    refine ⟨60216689062484414100854027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40144459374989609400569351 60216689062484414100854027)
    ·
      refine ⟨90325033593726621151281041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60216689062484414100854027 90325033593726621151281041)
      ·
        refine ⟨67743775195294965863460781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90325033593726621151281041 67743775195294965863460781)
        ·
          refine ⟨25403915698235612198797793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67743775195294965863460781 25403915698235612198797793)
          ·
            refine ⟨19052936773676709149098345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25403915698235612198797793 19052936773676709149098345)
            ·
              refine ⟨14289702580257531861823759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19052936773676709149098345 14289702580257531861823759)
              ·
                refine ⟨21434553870386297792735639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14289702580257531861823759 21434553870386297792735639)
                ·
                  refine ⟨32151830805579446689103459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21434553870386297792735639 32151830805579446689103459)
                  ·
                    refine ⟨48227746208369170033655189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32151830805579446689103459 48227746208369170033655189)
                    ·
                      refine ⟨2260675603517304845327587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48227746208369170033655189 2260675603517304845327587)
                      ·
                        rfl

theorem cell23_4402650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 1, 1, 6].length) (baseStart_4402650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4402650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4402650 prefixEnd_4402650 := by exact prefixLift 4402650
  have htrace : WordTrace (prefixWord ++ tailWord_4402650) baseStart_4402650 baseEnd_4402650 := by
    simpa [prefixWord, tailWord_4402650, baseEnd_4402650] using wordTrace_append hprefix tailTrace_4402650
  have hstable : (prefixWord ++ tailWord_4402650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4402650).length < 2 ^ (prefixWord ++ tailWord_4402650).sum := by decide
  have hdescent : baseEnd_4402650 < baseStart_4402650 := by decide
  rcases family_descends (prefixWord ++ tailWord_4402650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4402657 : List Nat := [1, 2, 3, 1, 2, 4, 1, 1, 3, 2, 3]
def baseStart_4402657 : Nat := 118140960795 + 4402657 * 2 ^ 59
def prefixEnd_4402657 : Nat := 4983230072969 + 3 ^ 40 * 4402657 * 2
def baseEnd_4402657 : Nat := 2260679197881886317940055

theorem tailTrace_4402657 : CollatzResearch.WordTrace tailWord_4402657 prefixEnd_4402657 2260679197881886317940055 := by
  unfold tailWord_4402657
  simp only [CollatzResearch.WordTrace]
  refine ⟨160578092810933077797782225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107052061873955385198521483 160578092810933077797782225)
  ·
    refine ⟨120433569608199808348336669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160578092810933077797782225 120433569608199808348336669)
    ·
      refine ⟨45162588603074928130626251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120433569608199808348336669 45162588603074928130626251)
      ·
        refine ⟨67743882904612392195939377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45162588603074928130626251 67743882904612392195939377)
        ·
          refine ⟨50807912178459294146954533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67743882904612392195939377 50807912178459294146954533)
          ·
            refine ⟨9526483533461117652553975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50807912178459294146954533 9526483533461117652553975)
            ·
              refine ⟨14289725300191676478830963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9526483533461117652553975 14289725300191676478830963)
              ·
                refine ⟨21434587950287514718246445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14289725300191676478830963 21434587950287514718246445)
                ·
                  refine ⟨8037970481357818019342417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21434587950287514718246445 8037970481357818019342417)
                  ·
                    refine ⟨6028477861018363514506813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8037970481357818019342417 6028477861018363514506813)
                    ·
                      refine ⟨2260679197881886317940055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6028477861018363514506813 2260679197881886317940055)
                      ·
                        rfl

theorem cell23_4402657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 3, 2, 3].length) (baseStart_4402657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4402657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4402657 prefixEnd_4402657 := by exact prefixLift 4402657
  have htrace : WordTrace (prefixWord ++ tailWord_4402657) baseStart_4402657 baseEnd_4402657 := by
    simpa [prefixWord, tailWord_4402657, baseEnd_4402657] using wordTrace_append hprefix tailTrace_4402657
  have hstable : (prefixWord ++ tailWord_4402657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4402657).length < 2 ^ (prefixWord ++ tailWord_4402657).sum := by decide
  have hdescent : baseEnd_4402657 < baseStart_4402657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4402657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4402674 : List Nat := [3, 2, 1, 4, 1, 3, 1, 1, 1, 1, 5]
def baseStart_4402674 : Nat := 118140960795 + 4402674 * 2 ^ 59
def prefixEnd_4402674 : Nat := 4983230072969 + 3 ^ 40 * 4402674 * 2
def baseEnd_4402674 : Nat := 2260687927053012751427477

theorem tailTrace_4402674 : CollatzResearch.WordTrace tailWord_4402674 prefixEnd_4402674 2260687927053012751427477 := by
  unfold tailWord_4402674
  simp only [CollatzResearch.WordTrace]
  refine ⟨40144678212967872425287769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107052475234580993134100717 40144678212967872425287769)
  ·
    refine ⟨30108508659725904318965827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40144678212967872425287769 30108508659725904318965827)
    ·
      refine ⟨45162762989588856478448741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30108508659725904318965827 45162762989588856478448741)
      ·
        refine ⟨8468018060547910589709139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45162762989588856478448741 8468018060547910589709139)
        ·
          refine ⟨12702027090821865884563709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8468018060547910589709139 12702027090821865884563709)
          ·
            refine ⟨4763260159058199706711391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12702027090821865884563709 4763260159058199706711391)
            ·
              refine ⟨7144890238587299560067087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4763260159058199706711391 7144890238587299560067087)
              ·
                refine ⟨10717335357880949340100631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7144890238587299560067087 10717335357880949340100631)
                ·
                  refine ⟨16076003036821424010150947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10717335357880949340100631 16076003036821424010150947)
                  ·
                    refine ⟨24114004555232136015226421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16076003036821424010150947 24114004555232136015226421)
                    ·
                      refine ⟨2260687927053012751427477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24114004555232136015226421 2260687927053012751427477)
                      ·
                        rfl

theorem cell23_4402674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_4402674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4402674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4402674 prefixEnd_4402674 := by exact prefixLift 4402674
  have htrace : WordTrace (prefixWord ++ tailWord_4402674) baseStart_4402674 baseEnd_4402674 := by
    simpa [prefixWord, tailWord_4402674, baseEnd_4402674] using wordTrace_append hprefix tailTrace_4402674
  have hstable : (prefixWord ++ tailWord_4402674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4402674).length < 2 ^ (prefixWord ++ tailWord_4402674).sum := by decide
  have hdescent : baseEnd_4402674 < baseStart_4402674 := by decide
  rcases family_descends (prefixWord ++ tailWord_4402674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4402697 : List Nat := [1, 2, 1, 1, 3, 1, 3, 1, 5, 3, 2]
def baseStart_4402697 : Nat := 118140960795 + 4402697 * 2 ^ 59
def prefixEnd_4402697 : Nat := 4983230072969 + 3 ^ 40 * 4402697 * 2
def baseEnd_4402697 : Nat := 2260699737108066161439871

theorem tailTrace_4402697 : CollatzResearch.WordTrace tailWord_4402697 prefixEnd_4402697 2260699737108066161439871 := by
  unfold tailWord_4402697
  simp only [CollatzResearch.WordTrace]
  refine ⟨160579551730788164629238345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107053034487192109752825563 160579551730788164629238345)
  ·
    refine ⟨120434663798091123471928759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160579551730788164629238345 120434663798091123471928759)
    ·
      refine ⟨180651995697136685207893139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120434663798091123471928759 180651995697136685207893139)
      ·
        refine ⟨270977993545705027811839709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180651995697136685207893139 270977993545705027811839709)
        ·
          refine ⟨101616747579639385429439891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 270977993545705027811839709 101616747579639385429439891)
          ·
            refine ⟨152425121369459078144159837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101616747579639385429439891 152425121369459078144159837)
            ·
              refine ⟨57159420513547154304059939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 152425121369459078144159837 57159420513547154304059939)
              ·
                refine ⟨85739130770320731456089909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57159420513547154304059939 85739130770320731456089909)
                ·
                  refine ⟨8038043509717568574008429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 85739130770320731456089909 8038043509717568574008429)
                  ·
                    refine ⟨3014266316144088215253161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8038043509717568574008429 3014266316144088215253161)
                    ·
                      refine ⟨2260699737108066161439871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3014266316144088215253161 2260699737108066161439871)
                      ·
                        rfl

theorem cell23_4402697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 5, 3, 2].length) (baseStart_4402697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4402697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4402697 prefixEnd_4402697 := by exact prefixLift 4402697
  have htrace : WordTrace (prefixWord ++ tailWord_4402697) baseStart_4402697 baseEnd_4402697 := by
    simpa [prefixWord, tailWord_4402697, baseEnd_4402697] using wordTrace_append hprefix tailTrace_4402697
  have hstable : (prefixWord ++ tailWord_4402697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4402697).length < 2 ^ (prefixWord ++ tailWord_4402697).sum := by decide
  have hdescent : baseEnd_4402697 < baseStart_4402697 := by decide
  rcases family_descends (prefixWord ++ tailWord_4402697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4402714 : List Nat := [3, 1, 1, 3, 1, 1, 1, 6, 1, 3, 2]
def baseStart_4402714 : Nat := 118140960795 + 4402714 * 2 ^ 59
def prefixEnd_4402714 : Nat := 4983230072969 + 3 ^ 40 * 4402714 * 2
def baseEnd_4402714 : Nat := 2260708466279192594927293

theorem tailTrace_4402714 : CollatzResearch.WordTrace tailWord_4402714 prefixEnd_4402714 2260708466279192594927293 := by
  unfold tailWord_4402714
  simp only [CollatzResearch.WordTrace]
  refine ⟨40145042942931644133151799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107053447847817717688404797 40145042942931644133151799)
  ·
    refine ⟨60217564414397466199727699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40145042942931644133151799 60217564414397466199727699)
    ·
      refine ⟨90326346621596199299591549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60217564414397466199727699 90326346621596199299591549)
      ·
        refine ⟨33872379983098574737346831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90326346621596199299591549 33872379983098574737346831)
        ·
          refine ⟨50808569974647862106020247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33872379983098574737346831 50808569974647862106020247)
          ·
            refine ⟨76212854961971793159030371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50808569974647862106020247 76212854961971793159030371)
            ·
              refine ⟨114319282442957689738545557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76212854961971793159030371 114319282442957689738545557)
              ·
                refine ⟨5358716364513641706494323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 114319282442957689738545557 5358716364513641706494323)
                ·
                  refine ⟨8038074546770462559741485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5358716364513641706494323 8038074546770462559741485)
                  ·
                    refine ⟨3014277955038923459903057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8038074546770462559741485 3014277955038923459903057)
                    ·
                      refine ⟨2260708466279192594927293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3014277955038923459903057 2260708466279192594927293)
                      ·
                        rfl

theorem cell23_4402714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 6, 1, 3, 2].length) (baseStart_4402714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4402714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4402714 prefixEnd_4402714 := by exact prefixLift 4402714
  have htrace : WordTrace (prefixWord ++ tailWord_4402714) baseStart_4402714 baseEnd_4402714 := by
    simpa [prefixWord, tailWord_4402714, baseEnd_4402714] using wordTrace_append hprefix tailTrace_4402714
  have hstable : (prefixWord ++ tailWord_4402714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4402714).length < 2 ^ (prefixWord ++ tailWord_4402714).sum := by decide
  have hdescent : baseEnd_4402714 < baseStart_4402714 := by decide
  rcases family_descends (prefixWord ++ tailWord_4402714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4402781 : List Nat := [1, 4, 4, 2, 1, 1, 1, 1, 2, 1, 5]
def baseStart_4402781 : Nat := 118140960795 + 4402781 * 2 ^ 59
def prefixEnd_4402781 : Nat := 4983230072969 + 3 ^ 40 * 4402781 * 2
def baseEnd_4402781 : Nat := 2260742869483043832789485

theorem tailTrace_4402781 : CollatzResearch.WordTrace tailWord_4402781 prefixEnd_4402781 2260742869483043832789485 := by
  unfold tailWord_4402781
  simp only [CollatzResearch.WordTrace]
  refine ⟨160582615462483846975296197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107055076974989231316864131 160582615462483846975296197)
  ·
    refine ⟨30109240399215721307868037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 160582615462483846975296197 30109240399215721307868037)
    ·
      refine ⟨5645482574852947745225257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30109240399215721307868037 5645482574852947745225257)
      ·
        refine ⟨4234111931139710808918943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5645482574852947745225257 4234111931139710808918943)
        ·
          refine ⟨6351167896709566213378415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4234111931139710808918943 6351167896709566213378415)
          ·
            refine ⟨9526751845064349320067623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6351167896709566213378415 9526751845064349320067623)
            ·
              refine ⟨14290127767596523980101435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9526751845064349320067623 14290127767596523980101435)
              ·
                refine ⟨21435191651394785970152153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14290127767596523980101435 21435191651394785970152153)
                ·
                  refine ⟨16076393738546089477614115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21435191651394785970152153 16076393738546089477614115)
                  ·
                    refine ⟨24114590607819134216421173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16076393738546089477614115 24114590607819134216421173)
                    ·
                      refine ⟨2260742869483043832789485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24114590607819134216421173 2260742869483043832789485)
                      ·
                        rfl

theorem cell23_4402781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_4402781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4402781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4402781 prefixEnd_4402781 := by exact prefixLift 4402781
  have htrace : WordTrace (prefixWord ++ tailWord_4402781) baseStart_4402781 baseEnd_4402781 := by
    simpa [prefixWord, tailWord_4402781, baseEnd_4402781] using wordTrace_append hprefix tailTrace_4402781
  have hstable : (prefixWord ++ tailWord_4402781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4402781).length < 2 ^ (prefixWord ++ tailWord_4402781).sum := by decide
  have hdescent : baseEnd_4402781 < baseStart_4402781 := by decide
  rcases family_descends (prefixWord ++ tailWord_4402781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4402810 : List Nat := [3, 1, 1, 1, 1, 1, 1, 4, 2, 8]
def baseStart_4402810 : Nat := 118140960795 + 4402810 * 2 ^ 59
def prefixEnd_4402810 : Nat := 4983230072969 + 3 ^ 40 * 4402810 * 2
def baseEnd_4402810 : Nat := 753585920140674739775617

theorem tailTrace_4402810 : CollatzResearch.WordTrace tailWord_4402810 prefixEnd_4402810 753585920140674739775617 := by
  unfold tailWord_4402810
  simp only [CollatzResearch.WordTrace]
  refine ⟨40145918294844696232025471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107055782119585856618734589 40145918294844696232025471)
  ·
    refine ⟨60218877442267044348038207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40145918294844696232025471 60218877442267044348038207)
    ·
      refine ⟨90328316163400566522057311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60218877442267044348038207 90328316163400566522057311)
      ·
        refine ⟨135492474245100849783085967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90328316163400566522057311 135492474245100849783085967)
        ·
          refine ⟨203238711367651274674628951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135492474245100849783085967 203238711367651274674628951)
          ·
            refine ⟨304858067051476912011943427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203238711367651274674628951 304858067051476912011943427)
            ·
              refine ⟨457287100577215368017915141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 304858067051476912011943427 457287100577215368017915141)
              ·
                refine ⟨85741331358227881503359089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 457287100577215368017915141 85741331358227881503359089)
                ·
                  refine ⟨64305998518670911127519317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85741331358227881503359089 64305998518670911127519317)
                  ·
                    refine ⟨753585920140674739775617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 64305998518670911127519317 753585920140674739775617)
                    ·
                      rfl

theorem cell23_4402810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 2, 8].length) (baseStart_4402810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4402810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4402810 prefixEnd_4402810 := by exact prefixLift 4402810
  have htrace : WordTrace (prefixWord ++ tailWord_4402810) baseStart_4402810 baseEnd_4402810 := by
    simpa [prefixWord, tailWord_4402810, baseEnd_4402810] using wordTrace_append hprefix tailTrace_4402810
  have hstable : (prefixWord ++ tailWord_4402810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4402810).length < 2 ^ (prefixWord ++ tailWord_4402810).sum := by decide
  have hdescent : baseEnd_4402810 < baseStart_4402810 := by decide
  rcases family_descends (prefixWord ++ tailWord_4402810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4402827 : List Nat := [1, 1, 1, 1, 4, 1, 4, 1, 5, 4]
def baseStart_4402827 : Nat := 118140960795 + 4402827 * 2 ^ 59
def prefixEnd_4402827 : Nat := 4983230072969 + 3 ^ 40 * 4402827 * 2
def baseEnd_4402827 : Nat := 753588829864383550938091

theorem tailTrace_4402827 : CollatzResearch.WordTrace tailWord_4402827 prefixEnd_4402827 753588829864383550938091 := by
  unfold tailWord_4402827
  simp only [CollatzResearch.WordTrace]
  refine ⟨160584293220317196831470735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107056195480211464554313823 160584293220317196831470735)
  ·
    refine ⟨240876439830475795247206103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160584293220317196831470735 240876439830475795247206103)
    ·
      refine ⟨361314659745713692870809155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240876439830475795247206103 361314659745713692870809155)
      ·
        refine ⟨541971989618570539306213733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 361314659745713692870809155 541971989618570539306213733)
        ·
          refine ⟨101619748053481976119915075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 541971989618570539306213733 101619748053481976119915075)
          ·
            refine ⟨152429622080222964179872613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101619748053481976119915075 152429622080222964179872613)
            ·
              refine ⟨28580554140041805783726115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 152429622080222964179872613 28580554140041805783726115)
              ·
                refine ⟨42870831210062708675589173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28580554140041805783726115 42870831210062708675589173)
                ·
                  refine ⟨4019140425943378938336485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42870831210062708675589173 4019140425943378938336485)
                  ·
                    refine ⟨753588829864383550938091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4019140425943378938336485 753588829864383550938091)
                    ·
                      rfl

theorem cell23_4402827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 5, 4].length) (baseStart_4402827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4402827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4402827 prefixEnd_4402827 := by exact prefixLift 4402827
  have htrace : WordTrace (prefixWord ++ tailWord_4402827) baseStart_4402827 baseEnd_4402827 := by
    simpa [prefixWord, tailWord_4402827, baseEnd_4402827] using wordTrace_append hprefix tailTrace_4402827
  have hstable : (prefixWord ++ tailWord_4402827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4402827).length < 2 ^ (prefixWord ++ tailWord_4402827).sum := by decide
  have hdescent : baseEnd_4402827 < baseStart_4402827 := by decide
  rcases family_descends (prefixWord ++ tailWord_4402827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4402837 : List Nat := [1, 3, 2, 1, 1, 1, 1, 5, 1, 4, 3]
def baseStart_4402837 : Nat := 118140960795 + 4402837 * 2 ^ 59
def prefixEnd_4402837 : Nat := 4983230072969 + 3 ^ 40 * 4402837 * 2
def baseEnd_4402837 : Nat := 2260771624399695613689227

theorem tailTrace_4402837 : CollatzResearch.WordTrace tailWord_4402837 prefixEnd_4402837 2260771624399695613689227 := by
  unfold tailWord_4402837
  simp only [CollatzResearch.WordTrace]
  refine ⟨160584657950280968539334765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107056438633520645692889843 160584657950280968539334765)
  ·
    refine ⟨60219246731355363202250537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160584657950280968539334765 60219246731355363202250537)
    ·
      refine ⟨45164435048516522401687903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60219246731355363202250537 45164435048516522401687903)
      ·
        refine ⟨67746652572774783602531855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45164435048516522401687903 67746652572774783602531855)
        ·
          refine ⟨101619978859162175403797783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67746652572774783602531855 101619978859162175403797783)
          ·
            refine ⟨152429968288743263105696675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101619978859162175403797783 152429968288743263105696675)
            ·
              refine ⟨228644952433114894658545013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152429968288743263105696675 228644952433114894658545013)
              ·
                refine ⟨21435464290604521374238595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 228644952433114894658545013 21435464290604521374238595)
                ·
                  refine ⟨32153196435906782061357893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21435464290604521374238595 32153196435906782061357893)
                  ·
                    refine ⟨6028724331732521636504605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32153196435906782061357893 6028724331732521636504605)
                    ·
                      refine ⟨2260771624399695613689227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6028724331732521636504605 2260771624399695613689227)
                      ·
                        rfl

theorem cell23_4402837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 4, 3].length) (baseStart_4402837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4402837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4402837 prefixEnd_4402837 := by exact prefixLift 4402837
  have htrace : WordTrace (prefixWord ++ tailWord_4402837) baseStart_4402837 baseEnd_4402837 := by
    simpa [prefixWord, tailWord_4402837, baseEnd_4402837] using wordTrace_append hprefix tailTrace_4402837
  have hstable : (prefixWord ++ tailWord_4402837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4402837).length < 2 ^ (prefixWord ++ tailWord_4402837).sum := by decide
  have hdescent : baseEnd_4402837 < baseStart_4402837 := by decide
  rcases family_descends (prefixWord ++ tailWord_4402837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4402882 : List Nat := [3, 5, 1, 2, 2, 1, 1, 1, 2, 5]
def baseStart_4402882 : Nat := 118140960795 + 4402882 * 2 ^ 59
def prefixEnd_4402882 : Nat := 4983230072969 + 3 ^ 40 * 4402882 * 2
def baseEnd_4402882 : Nat := 753598243676382645875507

theorem tailTrace_4402882 : CollatzResearch.WordTrace tailWord_4402882 prefixEnd_4402882 753598243676382645875507 := by
  unfold tailWord_4402882
  simp only [CollatzResearch.WordTrace]
  refine ⟨40146574808779485306180725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107057532823411960816481933 40146574808779485306180725)
  ·
    refine ⟨3763741388323076747454443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40146574808779485306180725 3763741388323076747454443)
    ·
      refine ⟨5645612082484615121181665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3763741388323076747454443 5645612082484615121181665)
      ·
        refine ⟨4234209061863461340886249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5645612082484615121181665 4234209061863461340886249)
        ·
          refine ⟨3175656796397596005664687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4234209061863461340886249 3175656796397596005664687)
          ·
            refine ⟨4763485194596394008497031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3175656796397596005664687 4763485194596394008497031)
            ·
              refine ⟨7145227791894591012745547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4763485194596394008497031 7145227791894591012745547)
              ·
                refine ⟨10717841687841886519118321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7145227791894591012745547 10717841687841886519118321)
                ·
                  refine ⟨8038381265881414889338741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10717841687841886519118321 8038381265881414889338741)
                  ·
                    refine ⟨753598243676382645875507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8038381265881414889338741 753598243676382645875507)
                    ·
                      rfl

theorem cell23_4402882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_4402882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4402882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4402882 prefixEnd_4402882 := by exact prefixLift 4402882
  have htrace : WordTrace (prefixWord ++ tailWord_4402882) baseStart_4402882 baseEnd_4402882 := by
    simpa [prefixWord, tailWord_4402882, baseEnd_4402882] using wordTrace_append hprefix tailTrace_4402882
  have hstable : (prefixWord ++ tailWord_4402882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4402882).length < 2 ^ (prefixWord ++ tailWord_4402882).sum := by decide
  have hdescent : baseEnd_4402882 < baseStart_4402882 := by decide
  rcases family_descends (prefixWord ++ tailWord_4402882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4402887 : List Nat := [1, 1, 4, 1, 1, 1, 3, 3, 3, 5]
def baseStart_4402887 : Nat := 118140960795 + 4402887 * 2 ^ 59
def prefixEnd_4402887 : Nat := 4983230072969 + 3 ^ 40 * 4402887 * 2
def baseEnd_4402887 : Nat := 753599099477473472687999

theorem tailTrace_4402887 : CollatzResearch.WordTrace tailWord_4402887 prefixEnd_4402887 753599099477473472687999 := by
  unfold tailWord_4402887
  simp only [CollatzResearch.WordTrace]
  refine ⟨160586481600099827078654915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107057654400066551385769943 160586481600099827078654915)
  ·
    refine ⟨240879722400149740617982373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160586481600099827078654915 240879722400149740617982373)
    ·
      refine ⟨45164947950028076365871695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 240879722400149740617982373 45164947950028076365871695)
      ·
        refine ⟨67747421925042114548807543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45164947950028076365871695 67747421925042114548807543)
        ·
          refine ⟨101621132887563171823211315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67747421925042114548807543 101621132887563171823211315)
          ·
            refine ⟨152431699331344757734816973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101621132887563171823211315 152431699331344757734816973)
            ·
              refine ⟨57161887249254284150556365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 152431699331344757734816973 57161887249254284150556365)
              ·
                refine ⟨21435707718470356556458637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57161887249254284150556365 21435707718470356556458637)
                ·
                  refine ⟨8038390394426383708671989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21435707718470356556458637 8038390394426383708671989)
                  ·
                    refine ⟨753599099477473472687999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8038390394426383708671989 753599099477473472687999)
                    ·
                      rfl

theorem cell23_4402887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 3, 5].length) (baseStart_4402887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4402887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4402887 prefixEnd_4402887 := by exact prefixLift 4402887
  have htrace : WordTrace (prefixWord ++ tailWord_4402887) baseStart_4402887 baseEnd_4402887 := by
    simpa [prefixWord, tailWord_4402887, baseEnd_4402887] using wordTrace_append hprefix tailTrace_4402887
  have hstable : (prefixWord ++ tailWord_4402887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4402887).length < 2 ^ (prefixWord ++ tailWord_4402887).sum := by decide
  have hdescent : baseEnd_4402887 < baseStart_4402887 := by decide
  rcases family_descends (prefixWord ++ tailWord_4402887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4402904 : List Nat := [2, 1, 2, 2, 3, 1, 3, 3, 1, 5]
def baseStart_4402904 : Nat := 118140960795 + 4402904 * 2 ^ 59
def prefixEnd_4402904 : Nat := 4983230072969 + 3 ^ 40 * 4402904 * 2
def baseEnd_4402904 : Nat := 753602009201182283850473

theorem tailTrace_4402904 : CollatzResearch.WordTrace tailWord_4402904 prefixEnd_4402904 753602009201182283850473 := by
  unfold tailWord_4402904
  simp only [CollatzResearch.WordTrace]
  refine ⟨80293550820519119491011883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107058067760692159321349177 80293550820519119491011883)
  ·
    refine ⟨120440326230778679236517825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80293550820519119491011883 120440326230778679236517825)
    ·
      refine ⟨90330244673084009427388369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120440326230778679236517825 90330244673084009427388369)
      ·
        refine ⟨67747683504813007070541277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90330244673084009427388369 67747683504813007070541277)
        ·
          refine ⟨25405381314304877651452979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67747683504813007070541277 25405381314304877651452979)
          ·
            refine ⟨38108071971457316477179469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25405381314304877651452979 38108071971457316477179469)
            ·
              refine ⟨14290526989296493678942301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38108071971457316477179469 14290526989296493678942301)
              ·
                refine ⟨5358947620986185129603363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14290526989296493678942301 5358947620986185129603363)
                ·
                  refine ⟨8038421431479277694405045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5358947620986185129603363 8038421431479277694405045)
                  ·
                    refine ⟨753602009201182283850473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8038421431479277694405045 753602009201182283850473)
                    ·
                      rfl

theorem cell23_4402904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 3, 1, 5].length) (baseStart_4402904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4402904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4402904 prefixEnd_4402904 := by exact prefixLift 4402904
  have htrace : WordTrace (prefixWord ++ tailWord_4402904) baseStart_4402904 baseEnd_4402904 := by
    simpa [prefixWord, tailWord_4402904, baseEnd_4402904] using wordTrace_append hprefix tailTrace_4402904
  have hstable : (prefixWord ++ tailWord_4402904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4402904).length < 2 ^ (prefixWord ++ tailWord_4402904).sum := by decide
  have hdescent : baseEnd_4402904 < baseStart_4402904 := by decide
  rcases family_descends (prefixWord ++ tailWord_4402904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4402908 : List Nat := [2, 2, 5, 1, 2, 2, 1, 2, 6]
def baseStart_4402908 : Nat := 118140960795 + 4402908 * 2 ^ 59
def prefixEnd_4402908 : Nat := 4983230072969 + 3 ^ 40 * 4402908 * 2
def baseEnd_4402908 : Nat := 251200897947351648433489

theorem tailTrace_4402908 : CollatzResearch.WordTrace tailWord_4402908 prefixEnd_4402908 251200897947351648433489 := by
  unfold tailWord_4402908
  simp only [CollatzResearch.WordTrace]
  refine ⟨80293623766511873832584689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107058165022015831776779585 80293623766511873832584689)
  ·
    refine ⟨60220217824883905374438517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80293623766511873832584689 60220217824883905374438517)
    ·
      refine ⟨5645645421082866128853611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 60220217824883905374438517 5645645421082866128853611)
      ·
        refine ⟨8468468131624299193280417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5645645421082866128853611 8468468131624299193280417)
        ·
          refine ⟨6351351098718224394960313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8468468131624299193280417 6351351098718224394960313)
          ·
            refine ⟨4763513324038668296220235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6351351098718224394960313 4763513324038668296220235)
            ·
              refine ⟨7145269986058002444330353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4763513324038668296220235 7145269986058002444330353)
              ·
                refine ⟨5358952489543501833247765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7145269986058002444330353 5358952489543501833247765)
                ·
                  refine ⟨251200897947351648433489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5358952489543501833247765 251200897947351648433489)
                  ·
                    rfl

theorem cell23_4402908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 2, 6].length) (baseStart_4402908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4402908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4402908 prefixEnd_4402908 := by exact prefixLift 4402908
  have htrace : WordTrace (prefixWord ++ tailWord_4402908) baseStart_4402908 baseEnd_4402908 := by
    simpa [prefixWord, tailWord_4402908, baseEnd_4402908] using wordTrace_append hprefix tailTrace_4402908
  have hstable : (prefixWord ++ tailWord_4402908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4402908).length < 2 ^ (prefixWord ++ tailWord_4402908).sum := by decide
  have hdescent : baseEnd_4402908 < baseStart_4402908 := by decide
  rcases family_descends (prefixWord ++ tailWord_4402908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4402941 : List Nat := [1, 4, 1, 1, 1, 1, 2, 3, 5, 2, 2]
def baseStart_4402941 : Nat := 118140960795 + 4402941 * 2 ^ 59
def prefixEnd_4402941 : Nat := 4983230072969 + 3 ^ 40 * 4402941 * 2
def baseEnd_4402941 : Nat := 2260825026387763206788749

theorem tailTrace_4402941 : CollatzResearch.WordTrace tailWord_4402941 prefixEnd_4402941 2260825026387763206788749 := by
  unfold tailWord_4402941
  simp only [CollatzResearch.WordTrace]
  refine ⟨160588451141904194301120677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107058967427936129534080451 160588451141904194301120677)
  ·
    refine ⟨30110334589107036431460127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 160588451141904194301120677 30110334589107036431460127)
    ·
      refine ⟨45165501883660554647190191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30110334589107036431460127 45165501883660554647190191)
      ·
        refine ⟨67748252825490831970785287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45165501883660554647190191 67748252825490831970785287)
        ·
          refine ⟨101622379238236247956177931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67748252825490831970785287 101622379238236247956177931)
          ·
            refine ⟨152433568857354371934266897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101622379238236247956177931 152433568857354371934266897)
            ·
              refine ⟨114325176643015778950700173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152433568857354371934266897 114325176643015778950700173)
              ·
                refine ⟨42871941241130917106512565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 114325176643015778950700173 42871941241130917106512565)
                ·
                  refine ⟨4019244491356023478735553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42871941241130917106512565 4019244491356023478735553)
                  ·
                    refine ⟨3014433368517017609051665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4019244491356023478735553 3014433368517017609051665)
                    ·
                      refine ⟨2260825026387763206788749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3014433368517017609051665 2260825026387763206788749)
                      ·
                        rfl

theorem cell23_4402941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 5, 2, 2].length) (baseStart_4402941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4402941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4402941 prefixEnd_4402941 := by exact prefixLift 4402941
  have htrace : WordTrace (prefixWord ++ tailWord_4402941) baseStart_4402941 baseEnd_4402941 := by
    simpa [prefixWord, tailWord_4402941, baseEnd_4402941] using wordTrace_append hprefix tailTrace_4402941
  have hstable : (prefixWord ++ tailWord_4402941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4402941).length < 2 ^ (prefixWord ++ tailWord_4402941).sum := by decide
  have hdescent : baseEnd_4402941 < baseStart_4402941 := by decide
  rcases family_descends (prefixWord ++ tailWord_4402941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4402991 : List Nat := [1, 1, 2, 1, 2, 1, 2, 7, 2, 1, 3]
def baseStart_4402991 : Nat := 118140960795 + 4402991 * 2 ^ 59
def prefixEnd_4402991 : Nat := 4983230072969 + 3 ^ 40 * 4402991 * 2
def baseEnd_4402991 : Nat := 2260850700420488011163519

theorem tailTrace_4402991 : CollatzResearch.WordTrace tailWord_4402991 prefixEnd_4402991 2260850700420488011163519 := by
  unfold tailWord_4402991
  simp only [CollatzResearch.WordTrace]
  refine ⟨160590274791723052840440827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107060183194482035226960551 160590274791723052840440827)
  ·
    refine ⟨240885412187584579260661241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160590274791723052840440827 240885412187584579260661241)
    ·
      refine ⟨180664059140688434445495931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 240885412187584579260661241 180664059140688434445495931)
      ·
        refine ⟨270996088711032651668243897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180664059140688434445495931 270996088711032651668243897)
        ·
          refine ⟨203247066533274488751182923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 270996088711032651668243897 203247066533274488751182923)
          ·
            refine ⟨304870599799911733126774385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203247066533274488751182923 304870599799911733126774385)
            ·
              refine ⟨228652949849933799845080789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 304870599799911733126774385 228652949849933799845080789)
              ·
                refine ⟨5359053512107823433869081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 228652949849933799845080789 5359053512107823433869081)
                ·
                  refine ⟨4019290134080867575401811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5359053512107823433869081 4019290134080867575401811)
                  ·
                    refine ⟨6028935201121301363102717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4019290134080867575401811 6028935201121301363102717)
                    ·
                      refine ⟨2260850700420488011163519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6028935201121301363102717 2260850700420488011163519)
                      ·
                        rfl

theorem cell23_4402991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 7, 2, 1, 3].length) (baseStart_4402991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4402991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4402991 prefixEnd_4402991 := by exact prefixLift 4402991
  have htrace : WordTrace (prefixWord ++ tailWord_4402991) baseStart_4402991 baseEnd_4402991 := by
    simpa [prefixWord, tailWord_4402991, baseEnd_4402991] using wordTrace_append hprefix tailTrace_4402991
  have hstable : (prefixWord ++ tailWord_4402991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4402991).length < 2 ^ (prefixWord ++ tailWord_4402991).sum := by decide
  have hdescent : baseEnd_4402991 < baseStart_4402991 := by decide
  rcases family_descends (prefixWord ++ tailWord_4402991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4402995 : List Nat := [1, 1, 1, 2, 8, 1, 1, 2, 1, 2, 3]
def baseStart_4402995 : Nat := 118140960795 + 4402995 * 2 ^ 59
def prefixEnd_4402995 : Nat := 4983230072969 + 3 ^ 40 * 4402995 * 2
def baseEnd_4402995 : Nat := 2260852754343105995513501

theorem tailTrace_4402995 : CollatzResearch.WordTrace tailWord_4402995 prefixEnd_4402995 2260852754343105995513501 := by
  unfold tailWord_4402995
  simp only [CollatzResearch.WordTrace]
  refine ⟨160590420683708561523586439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107060280455805707682390959 160590420683708561523586439)
  ·
    refine ⟨240885631025562842285379659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160590420683708561523586439 240885631025562842285379659)
    ·
      refine ⟨361328446538344263428069489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240885631025562842285379659 361328446538344263428069489)
      ·
        refine ⟨270996334903758197571052117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 361328446538344263428069489 270996334903758197571052117)
        ·
          refine ⟨3175738299653416377785767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 270996334903758197571052117 3175738299653416377785767)
          ·
            refine ⟨4763607449480124566678651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3175738299653416377785767 4763607449480124566678651)
            ·
              refine ⟨7145411174220186850017977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4763607449480124566678651 7145411174220186850017977)
              ·
                refine ⟨5359058380665140137513483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7145411174220186850017977 5359058380665140137513483)
                ·
                  refine ⟨8038587570997710206270225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5359058380665140137513483 8038587570997710206270225)
                  ·
                    refine ⟨6028940678248282654702669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8038587570997710206270225 6028940678248282654702669)
                    ·
                      refine ⟨2260852754343105995513501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6028940678248282654702669 2260852754343105995513501)
                      ·
                        rfl

theorem cell23_4402995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 2, 1, 2, 3].length) (baseStart_4402995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4402995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4402995 prefixEnd_4402995 := by exact prefixLift 4402995
  have htrace : WordTrace (prefixWord ++ tailWord_4402995) baseStart_4402995 baseEnd_4402995 := by
    simpa [prefixWord, tailWord_4402995, baseEnd_4402995] using wordTrace_append hprefix tailTrace_4402995
  have hstable : (prefixWord ++ tailWord_4402995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4402995).length < 2 ^ (prefixWord ++ tailWord_4402995).sum := by decide
  have hdescent : baseEnd_4402995 < baseStart_4402995 := by decide
  rcases family_descends (prefixWord ++ tailWord_4402995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4403027 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 6]
def baseStart_4403027 : Nat := 118140960795 + 4403027 * 2 ^ 59
def prefixEnd_4403027 : Nat := 4983230072969 + 3 ^ 40 * 4403027 * 2
def baseEnd_4403027 : Nat := 2260869185724049870313353

theorem tailTrace_4403027 : CollatzResearch.WordTrace tailWord_4403027 prefixEnd_4403027 2260869185724049870313353 := by
  unfold tailWord_4403027
  simp only [CollatzResearch.WordTrace]
  refine ⟨160591587819592630988751335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107061058546395087325834223 160591587819592630988751335)
  ·
    refine ⟨240887381729388946483127003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160591587819592630988751335 240887381729388946483127003)
    ·
      refine ⟨361331072594083419724690505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240887381729388946483127003 361331072594083419724690505)
      ·
        refine ⟨270998304445562564793517879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 361331072594083419724690505 270998304445562564793517879)
        ·
          refine ⟨406497456668343847190276819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270998304445562564793517879 406497456668343847190276819)
          ·
            refine ⟨609746185002515770785415229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 406497456668343847190276819 609746185002515770785415229)
            ·
              refine ⟨228654819375943414044530711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 609746185002515770785415229 228654819375943414044530711)
              ·
                refine ⟨342982229063915121066796067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 228654819375943414044530711 342982229063915121066796067)
                ·
                  refine ⟨514473343595872681600194101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 342982229063915121066796067 514473343595872681600194101)
                  ·
                    refine ⟨48231875962113063900018197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 514473343595872681600194101 48231875962113063900018197)
                    ·
                      refine ⟨2260869185724049870313353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48231875962113063900018197 2260869185724049870313353)
                      ·
                        rfl

theorem cell23_4403027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 6].length) (baseStart_4403027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4403027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4403027 prefixEnd_4403027 := by exact prefixLift 4403027
  have htrace : WordTrace (prefixWord ++ tailWord_4403027) baseStart_4403027 baseEnd_4403027 := by
    simpa [prefixWord, tailWord_4403027, baseEnd_4403027] using wordTrace_append hprefix tailTrace_4403027
  have hstable : (prefixWord ++ tailWord_4403027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4403027).length < 2 ^ (prefixWord ++ tailWord_4403027).sum := by decide
  have hdescent : baseEnd_4403027 < baseStart_4403027 := by decide
  rcases family_descends (prefixWord ++ tailWord_4403027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4403034 : List Nat := [3, 1, 1, 2, 1, 3, 1, 1, 1, 6, 3]
def baseStart_4403034 : Nat := 118140960795 + 4403034 * 2 ^ 59
def prefixEnd_4403034 : Nat := 4983230072969 + 3 ^ 40 * 4403034 * 2
def baseEnd_4403034 : Nat := 2260872780088631342925821

theorem tailTrace_4403034 : CollatzResearch.WordTrace tailWord_4403034 prefixEnd_4403034 2260872780088631342925821 := by
  unfold tailWord_4403034
  simp only [CollatzResearch.WordTrace]
  refine ⟨40147960782641817796064039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107061228753711514122837437 40147960782641817796064039)
  ·
    refine ⟨60221941173962726694096059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40147960782641817796064039 60221941173962726694096059)
    ·
      refine ⟨90332911760944090041144089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60221941173962726694096059 90332911760944090041144089)
      ·
        refine ⟨67749683820708067530858067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90332911760944090041144089 67749683820708067530858067)
        ·
          refine ⟨101624525731062101296287101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67749683820708067530858067 101624525731062101296287101)
          ·
            refine ⟨38109197149148287986107663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101624525731062101296287101 38109197149148287986107663)
            ·
              refine ⟨57163795723722431979161495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38109197149148287986107663 57163795723722431979161495)
              ·
                refine ⟨85745693585583647968742243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57163795723722431979161495 85745693585583647968742243)
                ·
                  refine ⟨128618540378375471953113365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85745693585583647968742243 128618540378375471953113365)
                  ·
                    refine ⟨6028994080236350247802189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 128618540378375471953113365 6028994080236350247802189)
                    ·
                      refine ⟨2260872780088631342925821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6028994080236350247802189 2260872780088631342925821)
                      ·
                        rfl

theorem cell23_4403034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 1, 6, 3].length) (baseStart_4403034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4403034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4403034 prefixEnd_4403034 := by exact prefixLift 4403034
  have htrace : WordTrace (prefixWord ++ tailWord_4403034) baseStart_4403034 baseEnd_4403034 := by
    simpa [prefixWord, tailWord_4403034, baseEnd_4403034] using wordTrace_append hprefix tailTrace_4403034
  have hstable : (prefixWord ++ tailWord_4403034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4403034).length < 2 ^ (prefixWord ++ tailWord_4403034).sum := by decide
  have hdescent : baseEnd_4403034 < baseStart_4403034 := by decide
  rcases family_descends (prefixWord ++ tailWord_4403034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4403048 : List Nat := [2, 1, 4, 2, 1, 1, 4, 1, 1, 4, 2]
def baseStart_4403048 : Nat := 118140960795 + 4403048 * 2 ^ 59
def prefixEnd_4403048 : Nat := 4983230072969 + 3 ^ 40 * 4403048 * 2
def baseEnd_4403048 : Nat := 2260879968817794288150757

theorem tailTrace_4403048 : CollatzResearch.WordTrace tailWord_4403048 prefixEnd_4403048 2260879968817794288150757 := by
  unfold tailWord_4403048
  simp only [CollatzResearch.WordTrace]
  refine ⟨80296176876258275787632899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107061569168344367716843865 80296176876258275787632899)
  ·
    refine ⟨120444265314387413681449349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80296176876258275787632899 120444265314387413681449349)
    ·
      refine ⟨22583299746447640065271753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120444265314387413681449349 22583299746447640065271753)
      ·
        refine ⟨16937474809835730048953815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22583299746447640065271753 16937474809835730048953815)
        ·
          refine ⟨25406212214753595073430723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16937474809835730048953815 25406212214753595073430723)
          ·
            refine ⟨38109318322130392610146085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25406212214753595073430723 38109318322130392610146085)
            ·
              refine ⟨7145497185399448614402391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38109318322130392610146085 7145497185399448614402391)
              ·
                refine ⟨10718245778099172921603587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7145497185399448614402391 10718245778099172921603587)
                ·
                  refine ⟨16077368667148759382405381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10718245778099172921603587 16077368667148759382405381)
                  ·
                    refine ⟨3014506625090392384201009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16077368667148759382405381 3014506625090392384201009)
                    ·
                      refine ⟨2260879968817794288150757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3014506625090392384201009 2260879968817794288150757)
                      ·
                        rfl

theorem cell23_4403048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 1, 1, 4, 2].length) (baseStart_4403048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4403048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4403048 prefixEnd_4403048 := by exact prefixLift 4403048
  have htrace : WordTrace (prefixWord ++ tailWord_4403048) baseStart_4403048 baseEnd_4403048 := by
    simpa [prefixWord, tailWord_4403048, baseEnd_4403048] using wordTrace_append hprefix tailTrace_4403048
  have hstable : (prefixWord ++ tailWord_4403048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4403048).length < 2 ^ (prefixWord ++ tailWord_4403048).sum := by decide
  have hdescent : baseEnd_4403048 < baseStart_4403048 := by decide
  rcases family_descends (prefixWord ++ tailWord_4403048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4403084 : List Nat := [2, 2, 1, 2, 1, 2, 1, 3, 4, 5]
def baseStart_4403084 : Nat := 118140960795 + 4403084 * 2 ^ 59
def prefixEnd_4403084 : Nat := 4983230072969 + 3 ^ 40 * 4403084 * 2
def baseEnd_4403084 : Nat := 753632818040452049100197

theorem tailTrace_4403084 : CollatzResearch.WordTrace tailWord_4403084 prefixEnd_4403084 753632818040452049100197 := by
  unfold tailWord_4403084
  simp only [CollatzResearch.WordTrace]
  refine ⟨80296833390193064861788153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107062444520257419815717537 80296833390193064861788153)
  ·
    refine ⟨60222625042644798646341115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80296833390193064861788153 60222625042644798646341115)
    ·
      refine ⟨90333937563967197969511673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60222625042644798646341115 90333937563967197969511673)
      ·
        refine ⟨67750453172975398477133755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90333937563967197969511673 67750453172975398477133755)
        ·
          refine ⟨101625679759463097715700633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67750453172975398477133755 101625679759463097715700633)
          ·
            refine ⟨76219259819597323286775475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101625679759463097715700633 76219259819597323286775475)
            ·
              refine ⟨114328889729395984930163213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76219259819597323286775475 114328889729395984930163213)
              ·
                refine ⟨42873333648523494348811205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 114328889729395984930163213 42873333648523494348811205)
                ·
                  refine ⟨8038750059098155190402101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42873333648523494348811205 8038750059098155190402101)
                  ·
                    refine ⟨753632818040452049100197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8038750059098155190402101 753632818040452049100197)
                    ·
                      rfl

theorem cell23_4403084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 4, 5].length) (baseStart_4403084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4403084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4403084 prefixEnd_4403084 := by exact prefixLift 4403084
  have htrace : WordTrace (prefixWord ++ tailWord_4403084) baseStart_4403084 baseEnd_4403084 := by
    simpa [prefixWord, tailWord_4403084, baseEnd_4403084] using wordTrace_append hprefix tailTrace_4403084
  have hstable : (prefixWord ++ tailWord_4403084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4403084).length < 2 ^ (prefixWord ++ tailWord_4403084).sum := by decide
  have hdescent : baseEnd_4403084 < baseStart_4403084 := by decide
  rcases family_descends (prefixWord ++ tailWord_4403084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4403121 : List Nat := [1, 2, 2, 4, 2, 1, 2, 1, 1, 3, 4]
def baseStart_4403121 : Nat := 118140960795 + 4403121 * 2 ^ 59
def prefixEnd_4403121 : Nat := 4983230072969 + 3 ^ 40 * 4403121 * 2
def baseEnd_4403121 : Nat := 2260917452905572502537921

theorem tailTrace_4403121 : CollatzResearch.WordTrace tailWord_4403121 prefixEnd_4403121 2260917452905572502537921 := by
  unfold tailWord_4403121
  simp only [CollatzResearch.WordTrace]
  refine ⟨160595016281252085042673217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107063344187501390028448811 160595016281252085042673217)
  ·
    refine ⟨120446262210939063782004913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160595016281252085042673217 120446262210939063782004913)
    ·
      refine ⟨90334696658204297836503685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120446262210939063782004913 90334696658204297836503685)
      ·
        refine ⟨16937755623413305844344441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90334696658204297836503685 16937755623413305844344441)
        ·
          refine ⟨12703316717559979383258331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16937755623413305844344441 12703316717559979383258331)
          ·
            refine ⟨19054975076339969074887497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12703316717559979383258331 19054975076339969074887497)
            ·
              refine ⟨14291231307254976806165623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19054975076339969074887497 14291231307254976806165623)
              ·
                refine ⟨21436846960882465209248435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14291231307254976806165623 21436846960882465209248435)
                ·
                  refine ⟨32155270441323697813872653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21436846960882465209248435 32155270441323697813872653)
                  ·
                    refine ⟨12058226415496386680202245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32155270441323697813872653 12058226415496386680202245)
                    ·
                      refine ⟨2260917452905572502537921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12058226415496386680202245 2260917452905572502537921)
                      ·
                        rfl

theorem cell23_4403121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_4403121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4403121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4403121 prefixEnd_4403121 := by exact prefixLift 4403121
  have htrace : WordTrace (prefixWord ++ tailWord_4403121) baseStart_4403121 baseEnd_4403121 := by
    simpa [prefixWord, tailWord_4403121, baseEnd_4403121] using wordTrace_append hprefix tailTrace_4403121
  have hstable : (prefixWord ++ tailWord_4403121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4403121).length < 2 ^ (prefixWord ++ tailWord_4403121).sum := by decide
  have hdescent : baseEnd_4403121 < baseStart_4403121 := by decide
  rcases family_descends (prefixWord ++ tailWord_4403121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4403148 : List Nat := [2, 2, 1, 4, 1, 2, 3, 1, 3, 4]
def baseStart_4403148 : Nat := 118140960795 + 4403148 * 2 ^ 59
def prefixEnd_4403148 : Nat := 4983230072969 + 3 ^ 40 * 4403148 * 2
def baseEnd_4403148 : Nat := 753643772294414632300099

theorem tailTrace_4403148 : CollatzResearch.WordTrace tailWord_4403148 prefixEnd_4403148 753643772294414632300099 := by
  unfold tailWord_4403148
  simp only [CollatzResearch.WordTrace]
  refine ⟨80298000526077134326953049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107064000701436179102604065 80298000526077134326953049)
  ·
    refine ⟨60223500394557850745214787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80298000526077134326953049 60223500394557850745214787)
    ·
      refine ⟨90335250591836776117822181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60223500394557850745214787 90335250591836776117822181)
      ·
        refine ⟨16937859485969395522091659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90335250591836776117822181 16937859485969395522091659)
        ·
          refine ⟨25406789228954093283137489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16937859485969395522091659 25406789228954093283137489)
          ·
            refine ⟨19055091921715569962353117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25406789228954093283137489 19055091921715569962353117)
            ·
              refine ⟨7145659470643338735882419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19055091921715569962353117 7145659470643338735882419)
              ·
                refine ⟨10718489205965008103823629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7145659470643338735882419 10718489205965008103823629)
                ·
                  refine ⟨4019433452236878038933861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10718489205965008103823629 4019433452236878038933861)
                  ·
                    refine ⟨753643772294414632300099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4019433452236878038933861 753643772294414632300099)
                    ·
                      rfl

theorem cell23_4403148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 1, 3, 4].length) (baseStart_4403148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4403148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4403148 prefixEnd_4403148 := by exact prefixLift 4403148
  have htrace : WordTrace (prefixWord ++ tailWord_4403148) baseStart_4403148 baseEnd_4403148 := by
    simpa [prefixWord, tailWord_4403148, baseEnd_4403148] using wordTrace_append hprefix tailTrace_4403148
  have hstable : (prefixWord ++ tailWord_4403148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4403148).length < 2 ^ (prefixWord ++ tailWord_4403148).sum := by decide
  have hdescent : baseEnd_4403148 < baseStart_4403148 := by decide
  rcases family_descends (prefixWord ++ tailWord_4403148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4403175 : List Nat := [1, 1, 5, 2, 3, 1, 2, 1, 2, 2, 3]
def baseStart_4403175 : Nat := 118140960795 + 4403175 * 2 ^ 59
def prefixEnd_4403175 : Nat := 4983230072969 + 3 ^ 40 * 4403175 * 2
def baseEnd_4403175 : Nat := 2260945180860915291262673

theorem tailTrace_4403175 : CollatzResearch.WordTrace tailWord_4403175 prefixEnd_4403175 2260945180860915291262673 := by
  unfold tailWord_4403175
  simp only [CollatzResearch.WordTrace]
  refine ⟨160596985823056452265138979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107064657215370968176759319 160596985823056452265138979)
  ·
    refine ⟨240895478734584678397708469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160596985823056452265138979 240895478734584678397708469)
    ·
      refine ⟨22583951131367313599785169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 240895478734584678397708469 22583951131367313599785169)
      ·
        refine ⟨16937963348525485199838877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22583951131367313599785169 16937963348525485199838877)
        ·
          refine ⟨6351736255697056949939579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16937963348525485199838877 6351736255697056949939579)
          ·
            refine ⟨9527604383545585424909369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6351736255697056949939579 9527604383545585424909369)
            ·
              refine ⟨7145703287659189068682027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9527604383545585424909369 7145703287659189068682027)
              ·
                refine ⟨10718554931488783603023041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7145703287659189068682027 10718554931488783603023041)
                ·
                  refine ⟨8038916198616587702267281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10718554931488783603023041 8038916198616587702267281)
                  ·
                    refine ⟨6029187148962440776700461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8038916198616587702267281 6029187148962440776700461)
                    ·
                      refine ⟨2260945180860915291262673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6029187148962440776700461 2260945180860915291262673)
                      ·
                        rfl

theorem cell23_4403175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_4403175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4403175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4403175 prefixEnd_4403175 := by exact prefixLift 4403175
  have htrace : WordTrace (prefixWord ++ tailWord_4403175) baseStart_4403175 baseEnd_4403175 := by
    simpa [prefixWord, tailWord_4403175, baseEnd_4403175] using wordTrace_append hprefix tailTrace_4403175
  have hstable : (prefixWord ++ tailWord_4403175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4403175).length < 2 ^ (prefixWord ++ tailWord_4403175).sum := by decide
  have hdescent : baseEnd_4403175 < baseStart_4403175 := by decide
  rcases family_descends (prefixWord ++ tailWord_4403175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4403206 : List Nat := [6, 2, 1, 2, 1, 1, 1, 1, 2, 4, 2]
def baseStart_4403206 : Nat := 118140960795 + 4403206 * 2 ^ 59
def prefixEnd_4403206 : Nat := 4983230072969 + 3 ^ 40 * 4403206 * 2
def baseEnd_4403206 : Nat := 2260961098761204669975031

theorem tailTrace_4403206 : CollatzResearch.WordTrace tailWord_4403206 prefixEnd_4403206 2260961098761204669975031 := by
  unfold tailWord_4403206
  simp only [CollatzResearch.WordTrace]
  refine ⟨5018691140185754517484921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 107065410990629429706344981 5018691140185754517484921)
  ·
    refine ⟨3764018355139315888113691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5018691140185754517484921 3764018355139315888113691)
    ·
      refine ⟨5646027532708973832170537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3764018355139315888113691 5646027532708973832170537)
      ·
        refine ⟨4234520649531730374127903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5646027532708973832170537 4234520649531730374127903)
        ·
          refine ⟨6351780974297595561191855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4234520649531730374127903 6351780974297595561191855)
          ·
            refine ⟨9527671461446393341787783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6351780974297595561191855 9527671461446393341787783)
            ·
              refine ⟨14291507192169590012681675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9527671461446393341787783 14291507192169590012681675)
              ·
                refine ⟨21437260788254385019022513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14291507192169590012681675 21437260788254385019022513)
                ·
                  refine ⟨16077945591190788764266885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21437260788254385019022513 16077945591190788764266885)
                  ·
                    refine ⟨3014614798348272893300041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16077945591190788764266885 3014614798348272893300041)
                    ·
                      refine ⟨2260961098761204669975031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3014614798348272893300041 2260961098761204669975031)
                      ·
                        rfl

theorem cell23_4403206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_4403206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4403206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4403206 prefixEnd_4403206 := by exact prefixLift 4403206
  have htrace : WordTrace (prefixWord ++ tailWord_4403206) baseStart_4403206 baseEnd_4403206 := by
    simpa [prefixWord, tailWord_4403206, baseEnd_4403206] using wordTrace_append hprefix tailTrace_4403206
  have hstable : (prefixWord ++ tailWord_4403206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4403206).length < 2 ^ (prefixWord ++ tailWord_4403206).sum := by decide
  have hdescent : baseEnd_4403206 < baseStart_4403206 := by decide
  rcases family_descends (prefixWord ++ tailWord_4403206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4403211 : List Nat := [1, 1, 1, 1, 6, 1, 1, 1, 5, 1, 4]
def baseStart_4403211 : Nat := 118140960795 + 4403211 * 2 ^ 59
def prefixEnd_4403211 : Nat := 4983230072969 + 3 ^ 40 * 4403211 * 2
def baseEnd_4403211 : Nat := 2260963666164477150412507

theorem tailTrace_4403211 : CollatzResearch.WordTrace tailWord_4403211 prefixEnd_4403211 2260963666164477150412507 := by
  unfold tailWord_4403211
  simp only [CollatzResearch.WordTrace]
  refine ⟨160598298850926030413449487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107065532567284020275632991 160598298850926030413449487)
  ·
    refine ⟨240897448276389045620174231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160598298850926030413449487 240897448276389045620174231)
    ·
      refine ⟨361346172414583568430261347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240897448276389045620174231 361346172414583568430261347)
      ·
        refine ⟨542019258621875352645392021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 361346172414583568430261347 542019258621875352645392021)
        ·
          refine ⟨25407152747900407155252751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 542019258621875352645392021 25407152747900407155252751)
          ·
            refine ⟨38110729121850610732879127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25407152747900407155252751 38110729121850610732879127)
            ·
              refine ⟨57166093682775916099318691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38110729121850610732879127 57166093682775916099318691)
              ·
                refine ⟨85749140524163874148978037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57166093682775916099318691 85749140524163874148978037)
                ·
                  refine ⟨8038981924140363201466691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 85749140524163874148978037 8038981924140363201466691)
                  ·
                    refine ⟨12058472886210544802200037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8038981924140363201466691 12058472886210544802200037)
                    ·
                      refine ⟨2260963666164477150412507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12058472886210544802200037 2260963666164477150412507)
                      ·
                        rfl

theorem cell23_4403211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 5, 1, 4].length) (baseStart_4403211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4403211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4403211 prefixEnd_4403211 := by exact prefixLift 4403211
  have htrace : WordTrace (prefixWord ++ tailWord_4403211) baseStart_4403211 baseEnd_4403211 := by
    simpa [prefixWord, tailWord_4403211, baseEnd_4403211] using wordTrace_append hprefix tailTrace_4403211
  have hstable : (prefixWord ++ tailWord_4403211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4403211).length < 2 ^ (prefixWord ++ tailWord_4403211).sum := by decide
  have hdescent : baseEnd_4403211 < baseStart_4403211 := by decide
  rcases family_descends (prefixWord ++ tailWord_4403211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4403228 : List Nat := [2, 2, 3, 1, 3, 1, 2, 1, 3, 1, 4]
def baseStart_4403228 : Nat := 118140960795 + 4403228 * 2 ^ 59
def prefixEnd_4403228 : Nat := 4983230072969 + 3 ^ 40 * 4403228 * 2
def baseEnd_4403228 : Nat := 2260972395335603583899929

theorem tailTrace_4403228 : CollatzResearch.WordTrace tailWord_4403228 prefixEnd_4403228 2260972395335603583899929 := by
  unfold tailWord_4403228
  simp only [CollatzResearch.WordTrace]
  refine ⟨80299459445932221158409169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107065945927909628211212225 80299459445932221158409169)
  ·
    refine ⟨60224594584449165868806877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80299459445932221158409169 60224594584449165868806877)
    ·
      refine ⟨22584222969168437200802579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60224594584449165868806877 22584222969168437200802579)
      ·
        refine ⟨33876334453752655801203869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22584222969168437200802579 33876334453752655801203869)
        ·
          refine ⟨12703625420157245925451451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33876334453752655801203869 12703625420157245925451451)
          ·
            refine ⟨19055438130235868888177177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12703625420157245925451451 19055438130235868888177177)
            ·
              refine ⟨14291578597676901666132883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19055438130235868888177177 14291578597676901666132883)
              ·
                refine ⟨21437367896515352499199325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14291578597676901666132883 21437367896515352499199325)
                ·
                  refine ⟨8039012961193257187199747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21437367896515352499199325 8039012961193257187199747)
                  ·
                    refine ⟨12058519441789885780799621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8039012961193257187199747 12058519441789885780799621)
                    ·
                      refine ⟨2260972395335603583899929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12058519441789885780799621 2260972395335603583899929)
                      ·
                        rfl

theorem cell23_4403228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_4403228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4403228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4403228 prefixEnd_4403228 := by exact prefixLift 4403228
  have htrace : WordTrace (prefixWord ++ tailWord_4403228) baseStart_4403228 baseEnd_4403228 := by
    simpa [prefixWord, tailWord_4403228, baseEnd_4403228] using wordTrace_append hprefix tailTrace_4403228
  have hstable : (prefixWord ++ tailWord_4403228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4403228).length < 2 ^ (prefixWord ++ tailWord_4403228).sum := by decide
  have hdescent : baseEnd_4403228 < baseStart_4403228 := by decide
  rcases family_descends (prefixWord ++ tailWord_4403228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4403242 : List Nat := [3, 1, 4, 1, 2, 3, 2, 1, 1, 5]
def baseStart_4403242 : Nat := 118140960795 + 4403242 * 2 ^ 59
def prefixEnd_4403242 : Nat := 4983230072969 + 3 ^ 40 * 4403242 * 2
def baseEnd_4403242 : Nat := 753659861354922176374955

theorem tailTrace_4403242 : CollatzResearch.WordTrace tailWord_4403242 prefixEnd_4403242 753659861354922176374955 := by
  unfold tailWord_4403242
  simp only [CollatzResearch.WordTrace]
  refine ⟨40149857378453430676956995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107066286342542481805218653 40149857378453430676956995)
  ·
    refine ⟨60224786067680146015435493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40149857378453430676956995 60224786067680146015435493)
    ·
      refine ⟨11292147387690027377894155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60224786067680146015435493 11292147387690027377894155)
      ·
        refine ⟨16938221081535041066841233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11292147387690027377894155 16938221081535041066841233)
        ·
          refine ⟨12703665811151280800130925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16938221081535041066841233 12703665811151280800130925)
          ·
            refine ⟨4763874679181730300049097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12703665811151280800130925 4763874679181730300049097)
            ·
              refine ⟨3572906009386297725036823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4763874679181730300049097 3572906009386297725036823)
              ·
                refine ⟨5359359014079446587555235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3572906009386297725036823 5359359014079446587555235)
                ·
                  refine ⟨8039038521119169881332853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5359359014079446587555235 8039038521119169881332853)
                  ·
                    refine ⟨753659861354922176374955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8039038521119169881332853 753659861354922176374955)
                    ·
                      rfl

theorem cell23_4403242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_4403242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4403242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4403242 prefixEnd_4403242 := by exact prefixLift 4403242
  have htrace : WordTrace (prefixWord ++ tailWord_4403242) baseStart_4403242 baseEnd_4403242 := by
    simpa [prefixWord, tailWord_4403242, baseEnd_4403242] using wordTrace_append hprefix tailTrace_4403242
  have hstable : (prefixWord ++ tailWord_4403242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4403242).length < 2 ^ (prefixWord ++ tailWord_4403242).sum := by decide
  have hdescent : baseEnd_4403242 < baseStart_4403242 := by decide
  rcases family_descends (prefixWord ++ tailWord_4403242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4403282 : List Nat := [3, 2, 2, 1, 4, 1, 2, 2, 1, 2, 3]
def baseStart_4403282 : Nat := 118140960795 + 4403282 * 2 ^ 59
def prefixEnd_4403282 : Nat := 4983230072969 + 3 ^ 40 * 4403282 * 2
def baseEnd_4403282 : Nat := 2261000123290946372624681

theorem tailTrace_4403282 : CollatzResearch.WordTrace tailWord_4403282 prefixEnd_4403282 2261000123290946372624681 := by
  unfold tailWord_4403282
  simp only [CollatzResearch.WordTrace]
  refine ⟨40150222108417202384821025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107067258955779206359522733 40150222108417202384821025)
  ·
    refine ⟨30112666581312901788615769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40150222108417202384821025 30112666581312901788615769)
    ·
      refine ⟨22584499935984676341461827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30112666581312901788615769 22584499935984676341461827)
      ·
        refine ⟨33876749903977014512192741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22584499935984676341461827 33876749903977014512192741)
        ·
          refine ⟨6351890606995690221036139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33876749903977014512192741 6351890606995690221036139)
          ·
            refine ⟨9527835910493535331554209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6351890606995690221036139 9527835910493535331554209)
            ·
              refine ⟨7145876932870151498665657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9527835910493535331554209 7145876932870151498665657)
              ·
                refine ⟨5359407699652613623999243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7145876932870151498665657 5359407699652613623999243)
                ·
                  refine ⟨8039111549478920435998865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5359407699652613623999243 8039111549478920435998865)
                  ·
                    refine ⟨6029333662109190326999149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8039111549478920435998865 6029333662109190326999149)
                    ·
                      refine ⟨2261000123290946372624681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6029333662109190326999149 2261000123290946372624681)
                      ·
                        rfl

theorem cell23_4403282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 2, 1, 2, 3].length) (baseStart_4403282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4403282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4403282 prefixEnd_4403282 := by exact prefixLift 4403282
  have htrace : WordTrace (prefixWord ++ tailWord_4403282) baseStart_4403282 baseEnd_4403282 := by
    simpa [prefixWord, tailWord_4403282, baseEnd_4403282] using wordTrace_append hprefix tailTrace_4403282
  have hstable : (prefixWord ++ tailWord_4403282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4403282).length < 2 ^ (prefixWord ++ tailWord_4403282).sum := by decide
  have hdescent : baseEnd_4403282 < baseStart_4403282 := by decide
  rcases family_descends (prefixWord ++ tailWord_4403282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4403305 : List Nat := [1, 2, 1, 1, 1, 5, 1, 5, 1, 3, 2]
def baseStart_4403305 : Nat := 118140960795 + 4403305 * 2 ^ 59
def prefixEnd_4403305 : Nat := 4983230072969 + 3 ^ 40 * 4403305 * 2
def baseEnd_4403305 : Nat := 2261011933345999782637075

theorem tailTrace_4403305 : CollatzResearch.WordTrace tailWord_4403305 prefixEnd_4403305 2261011933345999782637075 := by
  unfold tailWord_4403305
  simp only [CollatzResearch.WordTrace]
  refine ⟨160601727312585484467371369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107067818208390322978247579 160601727312585484467371369)
  ·
    refine ⟨120451295484439113350528527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160601727312585484467371369 120451295484439113350528527)
    ·
      refine ⟨180676943226658670025792791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120451295484439113350528527 180676943226658670025792791)
      ·
        refine ⟨271015414839988005038689187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180676943226658670025792791 271015414839988005038689187)
        ·
          refine ⟨406523122259982007558033781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271015414839988005038689187 406523122259982007558033781)
          ·
            refine ⟨38111542711873313208565667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 406523122259982007558033781 38111542711873313208565667)
            ·
              refine ⟨57167314067809969812848501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38111542711873313208565667 57167314067809969812848501)
              ·
                refine ⟨5359435693857184669954547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57167314067809969812848501 5359435693857184669954547)
                ·
                  refine ⟨8039153540785777004931821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5359435693857184669954547 8039153540785777004931821)
                  ·
                    refine ⟨3014682577794666376849433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8039153540785777004931821 3014682577794666376849433)
                    ·
                      refine ⟨2261011933345999782637075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3014682577794666376849433 2261011933345999782637075)
                      ·
                        rfl

theorem cell23_4403305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 5, 1, 3, 2].length) (baseStart_4403305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4403305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4403305 prefixEnd_4403305 := by exact prefixLift 4403305
  have htrace : WordTrace (prefixWord ++ tailWord_4403305) baseStart_4403305 baseEnd_4403305 := by
    simpa [prefixWord, tailWord_4403305, baseEnd_4403305] using wordTrace_append hprefix tailTrace_4403305
  have hstable : (prefixWord ++ tailWord_4403305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4403305).length < 2 ^ (prefixWord ++ tailWord_4403305).sum := by decide
  have hdescent : baseEnd_4403305 < baseStart_4403305 := by decide
  rcases family_descends (prefixWord ++ tailWord_4403305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4403338 : List Nat := [3, 1, 2, 3, 1, 2, 1, 2, 2, 1, 5]
def baseStart_4403338 : Nat := 118140960795 + 4403338 * 2 ^ 59
def prefixEnd_4403338 : Nat := 4983230072969 + 3 ^ 40 * 4403338 * 2
def baseEnd_4403338 : Nat := 2261028878207598153524423

theorem tailTrace_4403338 : CollatzResearch.WordTrace tailWord_4403338 prefixEnd_4403338 2261028878207598153524423 := by
  unfold tailWord_4403338
  simp only [CollatzResearch.WordTrace]
  refine ⟨40150732730366482775830667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107068620614310620735548445 40150732730366482775830667)
  ·
    refine ⟨60226099095549724163746001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40150732730366482775830667 60226099095549724163746001)
    ·
      refine ⟨45169574321662293122809501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60226099095549724163746001 45169574321662293122809501)
      ·
        refine ⟨16938590370623359921053563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45169574321662293122809501 16938590370623359921053563)
        ·
          refine ⟨25407885555935039881580345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16938590370623359921053563 25407885555935039881580345)
          ·
            refine ⟨19055914166951279911185259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25407885555935039881580345 19055914166951279911185259)
            ·
              refine ⟨28583871250426919866777889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19055914166951279911185259 28583871250426919866777889)
              ·
                refine ⟨21437903437820189900083417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28583871250426919866777889 21437903437820189900083417)
                ·
                  refine ⟨16078427578365142425062563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21437903437820189900083417 16078427578365142425062563)
                  ·
                    refine ⟨24117641367547713637593845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16078427578365142425062563 24117641367547713637593845)
                    ·
                      refine ⟨2261028878207598153524423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24117641367547713637593845 2261028878207598153524423)
                      ·
                        rfl

theorem cell23_4403338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_4403338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4403338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4403338 prefixEnd_4403338 := by exact prefixLift 4403338
  have htrace : WordTrace (prefixWord ++ tailWord_4403338) baseStart_4403338 baseEnd_4403338 := by
    simpa [prefixWord, tailWord_4403338, baseEnd_4403338] using wordTrace_append hprefix tailTrace_4403338
  have hstable : (prefixWord ++ tailWord_4403338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4403338).length < 2 ^ (prefixWord ++ tailWord_4403338).sum := by decide
  have hdescent : baseEnd_4403338 < baseStart_4403338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4403338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4403350 : List Nat := [5, 3, 2, 1, 1, 1, 3, 1, 1, 2, 3]
def baseStart_4403350 : Nat := 118140960795 + 4403350 * 2 ^ 59
def prefixEnd_4403350 : Nat := 4983230072969 + 3 ^ 40 * 4403350 * 2
def baseEnd_4403350 : Nat := 2261035039975452106574369

theorem tailTrace_4403350 : CollatzResearch.WordTrace tailWord_4403350 prefixEnd_4403350 2261035039975452106574369 := by
  unfold tailWord_4403350
  simp only [CollatzResearch.WordTrace]
  refine ⟨10037710537338903572047469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 107068912398281638101839669 10037710537338903572047469)
  ·
    refine ⟨3764141451502088839517801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10037710537338903572047469 3764141451502088839517801)
    ·
      refine ⟨2823106088626566629638351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3764141451502088839517801 2823106088626566629638351)
      ·
        refine ⟨4234659132939849944457527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2823106088626566629638351 4234659132939849944457527)
        ·
          refine ⟨6351988699409774916686291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4234659132939849944457527 6351988699409774916686291)
          ·
            refine ⟨9527983049114662375029437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6351988699409774916686291 9527983049114662375029437)
            ·
              refine ⟨3572993643417998390636039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9527983049114662375029437 3572993643417998390636039)
              ·
                refine ⟨5359490465126997585954059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3572993643417998390636039 5359490465126997585954059)
                ·
                  refine ⟨8039235697690496378931089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5359490465126997585954059 8039235697690496378931089)
                  ·
                    refine ⟨6029426773267872284198317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8039235697690496378931089 6029426773267872284198317)
                    ·
                      refine ⟨2261035039975452106574369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6029426773267872284198317 2261035039975452106574369)
                      ·
                        rfl

theorem cell23_4403350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_4403350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4403350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4403350 prefixEnd_4403350 := by exact prefixLift 4403350
  have htrace : WordTrace (prefixWord ++ tailWord_4403350) baseStart_4403350 baseEnd_4403350 := by
    simpa [prefixWord, tailWord_4403350, baseEnd_4403350] using wordTrace_append hprefix tailTrace_4403350
  have hstable : (prefixWord ++ tailWord_4403350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4403350).length < 2 ^ (prefixWord ++ tailWord_4403350).sum := by decide
  have hdescent : baseEnd_4403350 < baseStart_4403350 := by decide
  rcases family_descends (prefixWord ++ tailWord_4403350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4403352 : List Nat := [2, 1, 2, 4, 3, 1, 1, 2, 1, 4, 2]
def baseStart_4403352 : Nat := 118140960795 + 4403352 * 2 ^ 59
def prefixEnd_4403352 : Nat := 4983230072969 + 3 ^ 40 * 4403352 * 2
def baseEnd_4403352 : Nat := 2261036066936761098749359

theorem tailTrace_4403352 : CollatzResearch.WordTrace tailWord_4403352 prefixEnd_4403352 2261036066936761098749359 := by
  unfold tailWord_4403352
  simp only [CollatzResearch.WordTrace]
  refine ⟨80301720771707605747166155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107068961028943474329554873 80301720771707605747166155)
  ·
    refine ⟨120452581157561408620749233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80301720771707605747166155 120452581157561408620749233)
    ·
      refine ⟨90339435868171056465561925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120452581157561408620749233 90339435868171056465561925)
      ·
        refine ⟨16938644225282073087292861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90339435868171056465561925 16938644225282073087292861)
        ·
          refine ⟨6351991584480777407734823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16938644225282073087292861 6351991584480777407734823)
          ·
            refine ⟨9527987376721166111602235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6351991584480777407734823 9527987376721166111602235)
            ·
              refine ⟨14291981065081749167403353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9527987376721166111602235 14291981065081749167403353)
              ·
                refine ⟨10718985798811311875552515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14291981065081749167403353 10718985798811311875552515)
                ·
                  refine ⟨16078478698216967813328773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10718985798811311875552515 16078478698216967813328773)
                  ·
                    refine ⟨3014714755915681464999145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16078478698216967813328773 3014714755915681464999145)
                    ·
                      refine ⟨2261036066936761098749359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3014714755915681464999145 2261036066936761098749359)
                      ·
                        rfl

theorem cell23_4403352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 2, 1, 4, 2].length) (baseStart_4403352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4403352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4403352 prefixEnd_4403352 := by exact prefixLift 4403352
  have htrace : WordTrace (prefixWord ++ tailWord_4403352) baseStart_4403352 baseEnd_4403352 := by
    simpa [prefixWord, tailWord_4403352, baseEnd_4403352] using wordTrace_append hprefix tailTrace_4403352
  have hstable : (prefixWord ++ tailWord_4403352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4403352).length < 2 ^ (prefixWord ++ tailWord_4403352).sum := by decide
  have hdescent : baseEnd_4403352 < baseStart_4403352 := by decide
  rcases family_descends (prefixWord ++ tailWord_4403352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4403401 : List Nat := [1, 2, 1, 1, 2, 1, 1, 3, 1, 10]
def baseStart_4403401 : Nat := 118140960795 + 4403401 * 2 ^ 59
def prefixEnd_4403401 : Nat := 4983230072969 + 3 ^ 40 * 4403401 * 2
def baseEnd_4403401 : Nat := 753687075829610469012211

theorem tailTrace_4403401 : CollatzResearch.WordTrace tailWord_4403401 prefixEnd_4403401 753687075829610469012211 := by
  unfold tailWord_4403401
  simp only [CollatzResearch.WordTrace]
  refine ⟨160605228720237692862866057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107070152480158461908577371 160605228720237692862866057)
  ·
    refine ⟨120453921540178269647149543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160605228720237692862866057 120453921540178269647149543)
    ·
      refine ⟨180680882310267404470724315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120453921540178269647149543 180680882310267404470724315)
      ·
        refine ⟨271021323465401106706086473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180680882310267404470724315 271021323465401106706086473)
        ·
          refine ⟨203265992599050830029564855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 271021323465401106706086473 203265992599050830029564855)
          ·
            refine ⟨304898988898576245044347283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203265992599050830029564855 304898988898576245044347283)
            ·
              refine ⟨457348483347864367566520925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 304898988898576245044347283 457348483347864367566520925)
              ·
                refine ⟨171505681255449137837445347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 457348483347864367566520925 171505681255449137837445347)
                ·
                  refine ⟨257258521883173706756168021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 171505681255449137837445347 257258521883173706756168021)
                  ·
                    refine ⟨753687075829610469012211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 257258521883173706756168021 753687075829610469012211)
                    ·
                      rfl

theorem cell23_4403401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 10].length) (baseStart_4403401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4403401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4403401 prefixEnd_4403401 := by exact prefixLift 4403401
  have htrace : WordTrace (prefixWord ++ tailWord_4403401) baseStart_4403401 baseEnd_4403401 := by
    simpa [prefixWord, tailWord_4403401, baseEnd_4403401] using wordTrace_append hprefix tailTrace_4403401
  have hstable : (prefixWord ++ tailWord_4403401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4403401).length < 2 ^ (prefixWord ++ tailWord_4403401).sum := by decide
  have hdescent : baseEnd_4403401 < baseStart_4403401 := by decide
  rcases family_descends (prefixWord ++ tailWord_4403401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4403411 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 9]
def baseStart_4403411 : Nat := 118140960795 + 4403411 * 2 ^ 59
def prefixEnd_4403411 : Nat := 4983230072969 + 3 ^ 40 * 4403411 * 2
def baseEnd_4403411 : Nat := 2261066362295376367911587

theorem tailTrace_4403411 : CollatzResearch.WordTrace tailWord_4403411 prefixEnd_4403411 2261066362295376367911587 := by
  unfold tailWord_4403411
  simp only [CollatzResearch.WordTrace]
  refine ⟨160605593450201464570730087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107070395633467643047153391 160605593450201464570730087)
  ·
    refine ⟨240908390175302196856095131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160605593450201464570730087 240908390175302196856095131)
    ·
      refine ⟨361362585262953295284142697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240908390175302196856095131 361362585262953295284142697)
      ·
        refine ⟨271021938947214971463107023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 361362585262953295284142697 271021938947214971463107023)
        ·
          refine ⟨406532908420822457194660535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271021938947214971463107023 406532908420822457194660535)
          ·
            refine ⟨609799362631233685791990803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 406532908420822457194660535 609799362631233685791990803)
            ·
              refine ⟨914699043946850528687986205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 609799362631233685791990803 914699043946850528687986205)
              ·
                refine ⟨343012141480068948257994827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 914699043946850528687986205 343012141480068948257994827)
                ·
                  refine ⟨514518212220103422386992241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 343012141480068948257994827 514518212220103422386992241)
                  ·
                    refine ⟨385888659165077566790244181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 514518212220103422386992241 385888659165077566790244181)
                    ·
                      refine ⟨2261066362295376367911587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 385888659165077566790244181 2261066362295376367911587)
                      ·
                        rfl

theorem cell23_4403411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 9].length) (baseStart_4403411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4403411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4403411 prefixEnd_4403411 := by exact prefixLift 4403411
  have htrace : WordTrace (prefixWord ++ tailWord_4403411) baseStart_4403411 baseEnd_4403411 := by
    simpa [prefixWord, tailWord_4403411, baseEnd_4403411] using wordTrace_append hprefix tailTrace_4403411
  have hstable : (prefixWord ++ tailWord_4403411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4403411).length < 2 ^ (prefixWord ++ tailWord_4403411).sum := by decide
  have hdescent : baseEnd_4403411 < baseStart_4403411 := by decide
  rcases family_descends (prefixWord ++ tailWord_4403411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4403420 : List Nat := [2, 2, 5, 2, 2, 1, 1, 2, 2, 2, 2]
def baseStart_4403420 : Nat := 118140960795 + 4403420 * 2 ^ 59
def prefixEnd_4403420 : Nat := 4983230072969 + 3 ^ 40 * 4403420 * 2
def baseEnd_4403420 : Nat := 2261070983621266832699047

theorem tailTrace_4403420 : CollatzResearch.WordTrace tailWord_4403420 prefixEnd_4403420 2261070983621266832699047 := by
  unfold tailWord_4403420
  simp only [CollatzResearch.WordTrace]
  refine ⟨80302960853584429553903857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107070614471445906071871809 80302960853584429553903857)
  ·
    refine ⟨60227220640188322165427893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80302960853584429553903857 60227220640188322165427893)
    ·
      refine ⟨5646301935017655203008865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 60227220640188322165427893 5646301935017655203008865)
      ·
        refine ⟨4234726451263241402256649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5646301935017655203008865 4234726451263241402256649)
        ·
          refine ⟨3176044838447431051692487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4234726451263241402256649 3176044838447431051692487)
          ·
            refine ⟨4764067257671146577538731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3176044838447431051692487 4764067257671146577538731)
            ·
              refine ⟨7146100886506719866308097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4764067257671146577538731 7146100886506719866308097)
              ·
                refine ⟨5359575664880039899731073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7146100886506719866308097 5359575664880039899731073)
                ·
                  refine ⟨4019681748660029924798305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5359575664880039899731073 4019681748660029924798305)
                  ·
                    refine ⟨3014761311495022443598729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4019681748660029924798305 3014761311495022443598729)
                    ·
                      refine ⟨2261070983621266832699047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3014761311495022443598729 2261070983621266832699047)
                      ·
                        rfl

theorem cell23_4403420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_4403420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4403420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4403420 prefixEnd_4403420 := by exact prefixLift 4403420
  have htrace : WordTrace (prefixWord ++ tailWord_4403420) baseStart_4403420 baseEnd_4403420 := by
    simpa [prefixWord, tailWord_4403420, baseEnd_4403420] using wordTrace_append hprefix tailTrace_4403420
  have hstable : (prefixWord ++ tailWord_4403420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4403420).length < 2 ^ (prefixWord ++ tailWord_4403420).sum := by decide
  have hdescent : baseEnd_4403420 < baseStart_4403420 := by decide
  rcases family_descends (prefixWord ++ tailWord_4403420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4403425 : List Nat := [1, 2, 3, 1, 3, 1, 1, 1, 4, 4, 2]
def baseStart_4403425 : Nat := 118140960795 + 4403425 * 2 ^ 59
def prefixEnd_4403425 : Nat := 4983230072969 + 3 ^ 40 * 4403425 * 2
def baseEnd_4403425 : Nat := 2261073551024539313136523

theorem tailTrace_4403425 : CollatzResearch.WordTrace tailWord_4403425 prefixEnd_4403425 2261073551024539313136523 := by
  unfold tailWord_4403425
  simp only [CollatzResearch.WordTrace]
  refine ⟨160606104072150744961739729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107070736048100496641159819 160606104072150744961739729)
  ·
    refine ⟨120454578054113058721304797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160606104072150744961739729 120454578054113058721304797)
    ·
      refine ⟨45170466770292397020489299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120454578054113058721304797 45170466770292397020489299)
      ·
        refine ⟨67755700155438595530733949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45170466770292397020489299 67755700155438595530733949)
        ·
          refine ⟨25408387558289473324025231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67755700155438595530733949 25408387558289473324025231)
          ·
            refine ⟨38112581337434209986037847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25408387558289473324025231 38112581337434209986037847)
            ·
              refine ⟨57168872006151314979056771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38112581337434209986037847 57168872006151314979056771)
              ·
                refine ⟨85753308009226972468585157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57168872006151314979056771 85753308009226972468585157)
                ·
                  refine ⟨16078745251730057337859717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 85753308009226972468585157 16078745251730057337859717)
                  ·
                    refine ⟨3014764734699385750848697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16078745251730057337859717 3014764734699385750848697)
                    ·
                      refine ⟨2261073551024539313136523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3014764734699385750848697 2261073551024539313136523)
                      ·
                        rfl

theorem cell23_4403425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 4, 4, 2].length) (baseStart_4403425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4403425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4403425 prefixEnd_4403425 := by exact prefixLift 4403425
  have htrace : WordTrace (prefixWord ++ tailWord_4403425) baseStart_4403425 baseEnd_4403425 := by
    simpa [prefixWord, tailWord_4403425, baseEnd_4403425] using wordTrace_append hprefix tailTrace_4403425
  have hstable : (prefixWord ++ tailWord_4403425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4403425).length < 2 ^ (prefixWord ++ tailWord_4403425).sum := by decide
  have hdescent : baseEnd_4403425 < baseStart_4403425 := by decide
  rcases family_descends (prefixWord ++ tailWord_4403425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4403435 : List Nat := [1, 1, 1, 1, 2, 5, 4, 1, 3, 4]
def baseStart_4403435 : Nat := 118140960795 + 4403435 * 2 ^ 59
def prefixEnd_4403435 : Nat := 4983230072969 + 3 ^ 40 * 4403435 * 2
def baseEnd_4403435 : Nat := 753692895277028091337159

theorem tailTrace_4403435 : CollatzResearch.WordTrace tailWord_4403435 prefixEnd_4403435 753692895277028091337159 := by
  unfold tailWord_4403435
  simp only [CollatzResearch.WordTrace]
  refine ⟨160606468802114516669603759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107070979201409677779735839 160606468802114516669603759)
  ·
    refine ⟨240909703203171775004405639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160606468802114516669603759 240909703203171775004405639)
    ·
      refine ⟨361364554804757662506608459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240909703203171775004405639 361364554804757662506608459)
      ·
        refine ⟨542046832207136493759912689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 361364554804757662506608459 542046832207136493759912689)
        ·
          refine ⟨406535124155352370319934517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 542046832207136493759912689 406535124155352370319934517)
          ·
            refine ⟨38112667889564284717493861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 406535124155352370319934517 38112667889564284717493861)
            ·
              refine ⟨7146125229293303384530099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38112667889564284717493861 7146125229293303384530099)
              ·
                refine ⟨10719187843939955076795149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7146125229293303384530099 10719187843939955076795149)
                ·
                  refine ⟨4019695441477483153798181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10719187843939955076795149 4019695441477483153798181)
                  ·
                    refine ⟨753692895277028091337159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4019695441477483153798181 753692895277028091337159)
                    ·
                      rfl

theorem cell23_4403435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 1, 3, 4].length) (baseStart_4403435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4403435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4403435 prefixEnd_4403435 := by exact prefixLift 4403435
  have htrace : WordTrace (prefixWord ++ tailWord_4403435) baseStart_4403435 baseEnd_4403435 := by
    simpa [prefixWord, tailWord_4403435, baseEnd_4403435] using wordTrace_append hprefix tailTrace_4403435
  have hstable : (prefixWord ++ tailWord_4403435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4403435).length < 2 ^ (prefixWord ++ tailWord_4403435).sum := by decide
  have hdescent : baseEnd_4403435 < baseStart_4403435 := by decide
  rcases family_descends (prefixWord ++ tailWord_4403435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4403438 : List Nat := [4, 1, 2, 1, 1, 1, 1, 1, 4, 1, 6]
def baseStart_4403438 : Nat := 118140960795 + 4403438 * 2 ^ 59
def prefixEnd_4403438 : Nat := 4983230072969 + 3 ^ 40 * 4403438 * 2
def baseEnd_4403438 : Nat := 2261080226273047762273963

theorem tailTrace_4403438 : CollatzResearch.WordTrace tailWord_4403438 prefixEnd_4403438 2261080226273047762273963 := by
  unfold tailWord_4403438
  simp only [CollatzResearch.WordTrace]
  refine ⟨20075822277637956022745371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107071052147402432121308645 20075822277637956022745371)
  ·
    refine ⟨30113733416456934034118057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20075822277637956022745371 30113733416456934034118057)
    ·
      refine ⟨22585300062342700525588543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30113733416456934034118057 22585300062342700525588543)
      ·
        refine ⟨33877950093514050788382815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22585300062342700525588543 33877950093514050788382815)
        ·
          refine ⟨50816925140271076182574223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33877950093514050788382815 50816925140271076182574223)
          ·
            refine ⟨76225387710406614273861335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50816925140271076182574223 76225387710406614273861335)
            ·
              refine ⟨114338081565609921410792003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76225387710406614273861335 114338081565609921410792003)
              ·
                refine ⟨171507122348414882116188005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114338081565609921410792003 171507122348414882116188005)
                ·
                  refine ⟨32157585440327790396785251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 171507122348414882116188005 32157585440327790396785251)
                  ·
                    refine ⟨48236378160491685595177877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32157585440327790396785251 48236378160491685595177877)
                    ·
                      refine ⟨2261080226273047762273963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48236378160491685595177877 2261080226273047762273963)
                      ·
                        rfl

theorem cell23_4403438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_4403438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4403438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4403438 prefixEnd_4403438 := by exact prefixLift 4403438
  have htrace : WordTrace (prefixWord ++ tailWord_4403438) baseStart_4403438 baseEnd_4403438 := by
    simpa [prefixWord, tailWord_4403438, baseEnd_4403438] using wordTrace_append hprefix tailTrace_4403438
  have hstable : (prefixWord ++ tailWord_4403438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4403438).length < 2 ^ (prefixWord ++ tailWord_4403438).sum := by decide
  have hdescent : baseEnd_4403438 < baseStart_4403438 := by decide
  rcases family_descends (prefixWord ++ tailWord_4403438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4403442 : List Nat := [3, 2, 1, 3, 2, 1, 2, 1, 2, 4, 2]
def baseStart_4403442 : Nat := 118140960795 + 4403442 * 2 ^ 59
def prefixEnd_4403442 : Nat := 4983230072969 + 3 ^ 40 * 4403442 * 2
def baseEnd_4403442 : Nat := 2261082280195665746623945

theorem tailTrace_4403442 : CollatzResearch.WordTrace tailWord_4403442 prefixEnd_4403442 2261082280195665746623945 := by
  unfold tailWord_4403442
  simp only [CollatzResearch.WordTrace]
  refine ⟨40151681028272289216277145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107071149408726104576739053 40151681028272289216277145)
  ·
    refine ⟨30113760771204216912207859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40151681028272289216277145 30113760771204216912207859)
    ·
      refine ⟨45170641156806325368311789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30113760771204216912207859 45170641156806325368311789)
      ·
        refine ⟨16938990433802372013116921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45170641156806325368311789 16938990433802372013116921)
        ·
          refine ⟨12704242825351779009837691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16938990433802372013116921 12704242825351779009837691)
          ·
            refine ⟨19056364238027668514756537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12704242825351779009837691 19056364238027668514756537)
            ·
              refine ⟨14292273178520751386067403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19056364238027668514756537 14292273178520751386067403)
              ·
                refine ⟨21438409767781127079101105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14292273178520751386067403 21438409767781127079101105)
                ·
                  refine ⟨16078807325835845309325829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21438409767781127079101105 16078807325835845309325829)
                  ·
                    refine ⟨3014776373594220995498593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16078807325835845309325829 3014776373594220995498593)
                    ·
                      refine ⟨2261082280195665746623945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3014776373594220995498593 2261082280195665746623945)
                      ·
                        rfl

theorem cell23_4403442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 2, 4, 2].length) (baseStart_4403442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4403442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4403442 prefixEnd_4403442 := by exact prefixLift 4403442
  have htrace : WordTrace (prefixWord ++ tailWord_4403442) baseStart_4403442 baseEnd_4403442 := by
    simpa [prefixWord, tailWord_4403442, baseEnd_4403442] using wordTrace_append hprefix tailTrace_4403442
  have hstable : (prefixWord ++ tailWord_4403442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4403442).length < 2 ^ (prefixWord ++ tailWord_4403442).sum := by decide
  have hdescent : baseEnd_4403442 < baseStart_4403442 := by decide
  rcases family_descends (prefixWord ++ tailWord_4403442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4403448 : List Nat := [2, 1, 2, 1, 1, 2, 1, 7, 6]
def baseStart_4403448 : Nat := 118140960795 + 4403448 * 2 ^ 59
def prefixEnd_4403448 : Nat := 4983230072969 + 3 ^ 40 * 4403448 * 2
def baseEnd_4403448 : Nat := 251231706786621413683213

theorem tailTrace_4403448 : CollatzResearch.WordTrace tailWord_4403448 prefixEnd_4403448 251231706786621413683213 := by
  unfold tailWord_4403448
  simp only [CollatzResearch.WordTrace]
  refine ⟨80303471475533709944913499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107071295300711613259884665 80303471475533709944913499)
  ·
    refine ⟨120455207213300564917370249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80303471475533709944913499 120455207213300564917370249)
    ·
      refine ⟨90341405409975423688027687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120455207213300564917370249 90341405409975423688027687)
      ·
        refine ⟨135512108114963135532041531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90341405409975423688027687 135512108114963135532041531)
        ·
          refine ⟨203268162172444703298062297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135512108114963135532041531 203268162172444703298062297)
          ·
            refine ⟨152451121629333527473546723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 203268162172444703298062297 152451121629333527473546723)
            ·
              refine ⟨228676682444000291210320085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152451121629333527473546723 228676682444000291210320085)
              ·
                refine ⟨5359609744781256825241877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 228676682444000291210320085 5359609744781256825241877)
                ·
                  refine ⟨251231706786621413683213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5359609744781256825241877 251231706786621413683213)
                  ·
                    rfl

theorem cell23_4403448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 7, 6].length) (baseStart_4403448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4403448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4403448 prefixEnd_4403448 := by exact prefixLift 4403448
  have htrace : WordTrace (prefixWord ++ tailWord_4403448) baseStart_4403448 baseEnd_4403448 := by
    simpa [prefixWord, tailWord_4403448, baseEnd_4403448] using wordTrace_append hprefix tailTrace_4403448
  have hstable : (prefixWord ++ tailWord_4403448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4403448).length < 2 ^ (prefixWord ++ tailWord_4403448).sum := by decide
  have hdescent : baseEnd_4403448 < baseStart_4403448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4403448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4403475 : List Nat := [1, 1, 1, 2, 1, 3, 1, 4, 5, 1, 3]
def baseStart_4403475 : Nat := 118140960795 + 4403475 * 2 ^ 59
def prefixEnd_4403475 : Nat := 4983230072969 + 3 ^ 40 * 4403475 * 2
def baseEnd_4403475 : Nat := 2261099225057264117511293

theorem tailTrace_4403475 : CollatzResearch.WordTrace tailWord_4403475 prefixEnd_4403475 2261099225057264117511293 := by
  unfold tailWord_4403475
  simp only [CollatzResearch.WordTrace]
  refine ⟨160607927721969603501059879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107071951814646402334039919 160607927721969603501059879)
  ·
    refine ⟨240911891582954405251589819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160607927721969603501059879 240911891582954405251589819)
    ·
      refine ⟨361367837374431607877384729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240911891582954405251589819 361367837374431607877384729)
      ·
        refine ⟨271025878030823705908038547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 361367837374431607877384729 271025878030823705908038547)
        ·
          refine ⟨406538817046235558862057821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271025878030823705908038547 406538817046235558862057821)
          ·
            refine ⟨152452056392338334573271683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 406538817046235558862057821 152452056392338334573271683)
            ·
              refine ⟨228678084588507501859907525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152452056392338334573271683 228678084588507501859907525)
              ·
                refine ⟨42877140860345156598732661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 228678084588507501859907525 42877140860345156598732661)
                ·
                  refine ⟨4019731955657358431131187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42877140860345156598732661 4019731955657358431131187)
                  ·
                    refine ⟨6029597933486037646696781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4019731955657358431131187 6029597933486037646696781)
                    ·
                      refine ⟨2261099225057264117511293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6029597933486037646696781 2261099225057264117511293)
                      ·
                        rfl

theorem cell23_4403475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 5, 1, 3].length) (baseStart_4403475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4403475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4403475 prefixEnd_4403475 := by exact prefixLift 4403475
  have htrace : WordTrace (prefixWord ++ tailWord_4403475) baseStart_4403475 baseEnd_4403475 := by
    simpa [prefixWord, tailWord_4403475, baseEnd_4403475] using wordTrace_append hprefix tailTrace_4403475
  have hstable : (prefixWord ++ tailWord_4403475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4403475).length < 2 ^ (prefixWord ++ tailWord_4403475).sum := by decide
  have hdescent : baseEnd_4403475 < baseStart_4403475 := by decide
  rcases family_descends (prefixWord ++ tailWord_4403475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4403486 : List Nat := [4, 3, 2, 1, 1, 3, 1, 1, 3, 4]
def baseStart_4403486 : Nat := 118140960795 + 4403486 * 2 ^ 59
def prefixEnd_4403486 : Nat := 4983230072969 + 3 ^ 40 * 4403486 * 2
def baseEnd_4403486 : Nat := 753701624448154524824581

theorem tailTrace_4403486 : CollatzResearch.WordTrace tailWord_4403486 prefixEnd_4403486 753701624448154524824581 := by
  unfold tailWord_4403486
  simp only [CollatzResearch.WordTrace]
  refine ⟨20076041115616219047463789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107072219283286501586473541 20076041115616219047463789)
  ·
    refine ⟨7528515418356082142798921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20076041115616219047463789 7528515418356082142798921)
    ·
      refine ⟨5646386563767061607099191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7528515418356082142798921 5646386563767061607099191)
      ·
        refine ⟨8469579845650592410648787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5646386563767061607099191 8469579845650592410648787)
        ·
          refine ⟨12704369768475888615973181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8469579845650592410648787 12704369768475888615973181)
          ·
            refine ⟨4764138663178458230989943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12704369768475888615973181 4764138663178458230989943)
            ·
              refine ⟨7146207994767687346484915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4764138663178458230989943 7146207994767687346484915)
              ·
                refine ⟨10719311992151531019727373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7146207994767687346484915 10719311992151531019727373)
                ·
                  refine ⟨4019741997056824132397765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10719311992151531019727373 4019741997056824132397765)
                  ·
                    refine ⟨753701624448154524824581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4019741997056824132397765 753701624448154524824581)
                    ·
                      rfl

theorem cell23_4403486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_4403486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4403486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4403486 prefixEnd_4403486 := by exact prefixLift 4403486
  have htrace : WordTrace (prefixWord ++ tailWord_4403486) baseStart_4403486 baseEnd_4403486 := by
    simpa [prefixWord, tailWord_4403486, baseEnd_4403486] using wordTrace_append hprefix tailTrace_4403486
  have hstable : (prefixWord ++ tailWord_4403486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4403486).length < 2 ^ (prefixWord ++ tailWord_4403486).sum := by decide
  have hdescent : baseEnd_4403486 < baseStart_4403486 := by decide
  rcases family_descends (prefixWord ++ tailWord_4403486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4403562 : List Nat := [3, 1, 3, 3, 1, 1, 1, 3, 1, 2, 4]
def baseStart_4403562 : Nat := 118140960795 + 4403562 * 2 ^ 59
def prefixEnd_4403562 : Nat := 4983230072969 + 3 ^ 40 * 4403562 * 2
def baseEnd_4403562 : Nat := 2261143897874205277123393

theorem tailTrace_4403562 : CollatzResearch.WordTrace tailWord_4403562 prefixEnd_4403562 2261143897874205277123393 := by
  unfold tailWord_4403562
  simp only [CollatzResearch.WordTrace]
  refine ⟨40152775218163604339869235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107074067248436278239651293 40152775218163604339869235)
  ·
    refine ⟨60229162827245406509803853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40152775218163604339869235 60229162827245406509803853)
    ·
      refine ⟨22585936060217027441176445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60229162827245406509803853 22585936060217027441176445)
      ·
        refine ⟨8469726022581385290441167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22585936060217027441176445 8469726022581385290441167)
        ·
          refine ⟨12704589033872077935661751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8469726022581385290441167 12704589033872077935661751)
          ·
            refine ⟨19056883550808116903492627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12704589033872077935661751 19056883550808116903492627)
            ·
              refine ⟨28585325326212175355238941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19056883550808116903492627 28585325326212175355238941)
              ·
                refine ⟨10719496997329565758214603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28585325326212175355238941 10719496997329565758214603)
                ·
                  refine ⟨16079245495994348637321905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10719496997329565758214603 16079245495994348637321905)
                  ·
                    refine ⟨12059434121995761477991429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16079245495994348637321905 12059434121995761477991429)
                    ·
                      refine ⟨2261143897874205277123393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12059434121995761477991429 2261143897874205277123393)
                      ·
                        rfl

theorem cell23_4403562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_4403562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4403562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4403562 prefixEnd_4403562 := by exact prefixLift 4403562
  have htrace : WordTrace (prefixWord ++ tailWord_4403562) baseStart_4403562 baseEnd_4403562 := by
    simpa [prefixWord, tailWord_4403562, baseEnd_4403562] using wordTrace_append hprefix tailTrace_4403562
  have hstable : (prefixWord ++ tailWord_4403562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4403562).length < 2 ^ (prefixWord ++ tailWord_4403562).sum := by decide
  have hdescent : baseEnd_4403562 < baseStart_4403562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4403562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4403615 : List Nat := [1, 1, 2, 5, 1, 1, 1, 3, 2, 6]
def baseStart_4403615 : Nat := 118140960795 + 4403615 * 2 ^ 59
def prefixEnd_4403615 : Nat := 4983230072969 + 3 ^ 40 * 4403615 * 2
def baseEnd_4403615 : Nat := 753723704116297856586883

theorem tailTrace_4403615 : CollatzResearch.WordTrace tailWord_4403615 prefixEnd_4403615 753723704116297856586883 := by
  unfold tailWord_4403615
  simp only [CollatzResearch.WordTrace]
  refine ⟨160613033941462407411156299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107075355960974938274104199 160613033941462407411156299)
  ·
    refine ⟨240919550912193611116734449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160613033941462407411156299 240919550912193611116734449)
    ·
      refine ⟨180689663184145208337550837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 240919550912193611116734449 180689663184145208337550837)
      ·
        refine ⟨16939655923513613281645391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 180689663184145208337550837 16939655923513613281645391)
        ·
          refine ⟨25409483885270419922468087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16939655923513613281645391 25409483885270419922468087)
          ·
            refine ⟨38114225827905629883702131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25409483885270419922468087 38114225827905629883702131)
            ·
              refine ⟨57171338741858444825553197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38114225827905629883702131 57171338741858444825553197)
              ·
                refine ⟨21439252028196916809582449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57171338741858444825553197 21439252028196916809582449)
                ·
                  refine ⟨16079439021147687607186837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21439252028196916809582449 16079439021147687607186837)
                  ·
                    refine ⟨753723704116297856586883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16079439021147687607186837 753723704116297856586883)
                    ·
                      rfl

theorem cell23_4403615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 2, 6].length) (baseStart_4403615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4403615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4403615 prefixEnd_4403615 := by exact prefixLift 4403615
  have htrace : WordTrace (prefixWord ++ tailWord_4403615) baseStart_4403615 baseEnd_4403615 := by
    simpa [prefixWord, tailWord_4403615, baseEnd_4403615] using wordTrace_append hprefix tailTrace_4403615
  have hstable : (prefixWord ++ tailWord_4403615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4403615).length < 2 ^ (prefixWord ++ tailWord_4403615).sum := by decide
  have hdescent : baseEnd_4403615 < baseStart_4403615 := by decide
  rcases family_descends (prefixWord ++ tailWord_4403615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4403616 : List Nat := [2, 1, 1, 4, 1, 4, 3, 1, 2, 1, 3]
def baseStart_4403616 : Nat := 118140960795 + 4403616 * 2 ^ 59
def prefixEnd_4403616 : Nat := 4983230072969 + 3 ^ 40 * 4403616 * 2
def baseEnd_4403616 : Nat := 2261171625829548065848145

theorem tailTrace_4403616 : CollatzResearch.WordTrace tailWord_4403616 prefixEnd_4403616 2261171625829548065848145 := by
  unfold tailWord_4403616
  simp only [CollatzResearch.WordTrace]
  refine ⟨80306535207229392290971351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107075380276305856387961801 80306535207229392290971351)
  ·
    refine ⟨120459802810844088436457027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80306535207229392290971351 120459802810844088436457027)
    ·
      refine ⟨180689704216266132654685541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120459802810844088436457027 180689704216266132654685541)
      ·
        refine ⟨33879319540549899872753539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 180689704216266132654685541 33879319540549899872753539)
        ·
          refine ⟨50818979310824849809130309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33879319540549899872753539 50818979310824849809130309)
          ·
            refine ⟨9528558620779659339211933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50818979310824849809130309 9528558620779659339211933)
            ·
              refine ⟨3573209482792372252204475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9528558620779659339211933 3573209482792372252204475)
              ·
                refine ⟨5359814224188558378306713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3573209482792372252204475 5359814224188558378306713)
                ·
                  refine ⟨4019860668141418783730035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5359814224188558378306713 4019860668141418783730035)
                  ·
                    refine ⟨6029791002212128175595053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4019860668141418783730035 6029791002212128175595053)
                    ·
                      refine ⟨2261171625829548065848145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6029791002212128175595053 2261171625829548065848145)
                      ·
                        rfl

theorem cell23_4403616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 3, 1, 2, 1, 3].length) (baseStart_4403616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4403616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4403616 prefixEnd_4403616 := by exact prefixLift 4403616
  have htrace : WordTrace (prefixWord ++ tailWord_4403616) baseStart_4403616 baseEnd_4403616 := by
    simpa [prefixWord, tailWord_4403616, baseEnd_4403616] using wordTrace_append hprefix tailTrace_4403616
  have hstable : (prefixWord ++ tailWord_4403616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4403616).length < 2 ^ (prefixWord ++ tailWord_4403616).sum := by decide
  have hdescent : baseEnd_4403616 < baseStart_4403616 := by decide
  rcases family_descends (prefixWord ++ tailWord_4403616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4403625 : List Nat := [1, 2, 1, 1, 1, 1, 3, 4, 2, 4, 3]
def baseStart_4403625 : Nat := 118140960795 + 4403625 * 2 ^ 59
def prefixEnd_4403625 : Nat := 4983230072969 + 3 ^ 40 * 4403625 * 2
def baseEnd_4403625 : Nat := 2261176247155438530635603

theorem tailTrace_4403625 : CollatzResearch.WordTrace tailWord_4403625 prefixEnd_4403625 2261176247155438530635603 := by
  unfold tailWord_4403625
  simp only [CollatzResearch.WordTrace]
  refine ⟨160613398671426179119020329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107075599114284119412680219 160613398671426179119020329)
  ·
    refine ⟨120460049003569634339265247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160613398671426179119020329 120460049003569634339265247)
    ·
      refine ⟨180690073505354451508897871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120460049003569634339265247 180690073505354451508897871)
      ·
        refine ⟨271035110258031677263346807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180690073505354451508897871 271035110258031677263346807)
        ·
          refine ⟨406552665387047515895020211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271035110258031677263346807 406552665387047515895020211)
          ·
            refine ⟨609828998080571273842530317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 406552665387047515895020211 609828998080571273842530317)
            ·
              refine ⟨228685874280214227690948869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 609828998080571273842530317 228685874280214227690948869)
              ·
                refine ⟨42878601427540167692052913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 228685874280214227690948869 42878601427540167692052913)
                ·
                  refine ⟨32158951070655125769039685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42878601427540167692052913 32158951070655125769039685)
                  ·
                    refine ⟨6029803325747836081694941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32158951070655125769039685 6029803325747836081694941)
                    ·
                      refine ⟨2261176247155438530635603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6029803325747836081694941 2261176247155438530635603)
                      ·
                        rfl

theorem cell23_4403625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 4, 3].length) (baseStart_4403625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4403625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4403625 prefixEnd_4403625 := by exact prefixLift 4403625
  have htrace : WordTrace (prefixWord ++ tailWord_4403625) baseStart_4403625 baseEnd_4403625 := by
    simpa [prefixWord, tailWord_4403625, baseEnd_4403625] using wordTrace_append hprefix tailTrace_4403625
  have hstable : (prefixWord ++ tailWord_4403625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4403625).length < 2 ^ (prefixWord ++ tailWord_4403625).sum := by decide
  have hdescent : baseEnd_4403625 < baseStart_4403625 := by decide
  rcases family_descends (prefixWord ++ tailWord_4403625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4403639 : List Nat := [1, 1, 3, 1, 3, 3, 1, 2, 4, 2, 2]
def baseStart_4403639 : Nat := 118140960795 + 4403639 * 2 ^ 59
def prefixEnd_4403639 : Nat := 4983230072969 + 3 ^ 40 * 4403639 * 2
def baseEnd_4403639 : Nat := 2261183435884601475860539

theorem tailTrace_4403639 : CollatzResearch.WordTrace tailWord_4403639 prefixEnd_4403639 2261183435884601475860539 := by
  unfold tailWord_4403639
  simp only [CollatzResearch.WordTrace]
  refine ⟨160613909293375459510029971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107075939528916973006686647 160613909293375459510029971)
  ·
    refine ⟨240920863940063189265044957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160613909293375459510029971 240920863940063189265044957)
    ·
      refine ⟨90345323977523695974391859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 240920863940063189265044957 90345323977523695974391859)
      ·
        refine ⟨135517985966285543961587789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90345323977523695974391859 135517985966285543961587789)
        ·
          refine ⟨50819244737357078985595421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135517985966285543961587789 50819244737357078985595421)
          ·
            refine ⟨19057216776508904619598283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50819244737357078985595421 19057216776508904619598283)
            ·
              refine ⟨28585825164763356929397425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19057216776508904619598283 28585825164763356929397425)
              ·
                refine ⟨21439368873572517697048069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28585825164763356929397425 21439368873572517697048069)
                ·
                  refine ⟨4019881663794847068196513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21439368873572517697048069 4019881663794847068196513)
                  ·
                    refine ⟨3014911247846135301147385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4019881663794847068196513 3014911247846135301147385)
                    ·
                      refine ⟨2261183435884601475860539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3014911247846135301147385 2261183435884601475860539)
                      ·
                        rfl

theorem cell23_4403639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 4, 2, 2].length) (baseStart_4403639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4403639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4403639 prefixEnd_4403639 := by exact prefixLift 4403639
  have htrace : WordTrace (prefixWord ++ tailWord_4403639) baseStart_4403639 baseEnd_4403639 := by
    simpa [prefixWord, tailWord_4403639, baseEnd_4403639] using wordTrace_append hprefix tailTrace_4403639
  have hstable : (prefixWord ++ tailWord_4403639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4403639).length < 2 ^ (prefixWord ++ tailWord_4403639).sum := by decide
  have hdescent : baseEnd_4403639 < baseStart_4403639 := by decide
  rcases family_descends (prefixWord ++ tailWord_4403639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4403692 : List Nat := [2, 2, 1, 1, 2, 1, 6, 1, 2, 5]
def baseStart_4403692 : Nat := 118140960795 + 4403692 * 2 ^ 59
def prefixEnd_4403692 : Nat := 4983230072969 + 3 ^ 40 * 4403692 * 2
def baseEnd_4403692 : Nat := 753736883453096589499265

theorem tailTrace_4403692 : CollatzResearch.WordTrace tailWord_4403692 prefixEnd_4403692 753736883453096589499265 := by
  unfold tailWord_4403692
  simp only [CollatzResearch.WordTrace]
  refine ⟨80307921181091724780854665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107077228241455633041139553 80307921181091724780854665)
  ·
    refine ⟨60230940885818793585640999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80307921181091724780854665 60230940885818793585640999)
    ·
      refine ⟨90346411328728190378461499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60230940885818793585640999 90346411328728190378461499)
      ·
        refine ⟨135519616993092285567692249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90346411328728190378461499 135519616993092285567692249)
        ·
          refine ⟨101639712744819214175769187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135519616993092285567692249 101639712744819214175769187)
          ·
            refine ⟨152459569117228821263653781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101639712744819214175769187 152459569117228821263653781)
            ·
              refine ⟨7146542302370100996733771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 152459569117228821263653781 7146542302370100996733771)
              ·
                refine ⟨10719813453555151495100657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7146542302370100996733771 10719813453555151495100657)
                ·
                  refine ⟨8039860090166363621325493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10719813453555151495100657 8039860090166363621325493)
                  ·
                    refine ⟨753736883453096589499265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8039860090166363621325493 753736883453096589499265)
                    ·
                      rfl

theorem cell23_4403692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 5].length) (baseStart_4403692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4403692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4403692 prefixEnd_4403692 := by exact prefixLift 4403692
  have htrace : WordTrace (prefixWord ++ tailWord_4403692) baseStart_4403692 baseEnd_4403692 := by
    simpa [prefixWord, tailWord_4403692, baseEnd_4403692] using wordTrace_append hprefix tailTrace_4403692
  have hstable : (prefixWord ++ tailWord_4403692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4403692).length < 2 ^ (prefixWord ++ tailWord_4403692).sum := by decide
  have hdescent : baseEnd_4403692 < baseStart_4403692 := by decide
  rcases family_descends (prefixWord ++ tailWord_4403692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4403702 : List Nat := [5, 1, 1, 1, 2, 1, 1, 1, 3, 2, 5]
def baseStart_4403702 : Nat := 118140960795 + 4403702 * 2 ^ 59
def prefixEnd_4403702 : Nat := 4983230072969 + 3 ^ 40 * 4403702 * 2
def baseEnd_4403702 : Nat := 2261215785165834729372749

theorem tailTrace_4403702 : CollatzResearch.WordTrace tailWord_4403702 prefixEnd_4403702 2261215785165834729372749 := by
  unfold tailWord_4403702
  simp only [CollatzResearch.WordTrace]
  refine ⟨10038512943259201329348335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 107077471394764814179715573 10038512943259201329348335)
  ·
    refine ⟨15057769414888801994022503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10038512943259201329348335 15057769414888801994022503)
    ·
      refine ⟨22586654122333202991033755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15057769414888801994022503 22586654122333202991033755)
      ·
        refine ⟨33879981183499804486550633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22586654122333202991033755 33879981183499804486550633)
        ·
          refine ⟨25409985887624853364912975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33879981183499804486550633 25409985887624853364912975)
          ·
            refine ⟨38114978831437280047369463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25409985887624853364912975 38114978831437280047369463)
            ·
              refine ⟨57172468247155920071054195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38114978831437280047369463 57172468247155920071054195)
              ·
                refine ⟨85758702370733880106581293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57172468247155920071054195 85758702370733880106581293)
                ·
                  refine ⟨32159513389025205039967985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 85758702370733880106581293 32159513389025205039967985)
                  ·
                    refine ⟨24119635041768903779975989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32159513389025205039967985 24119635041768903779975989)
                    ·
                      refine ⟨2261215785165834729372749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24119635041768903779975989 2261215785165834729372749)
                      ·
                        rfl

theorem cell23_4403702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_4403702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4403702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4403702 prefixEnd_4403702 := by exact prefixLift 4403702
  have htrace : WordTrace (prefixWord ++ tailWord_4403702) baseStart_4403702 baseEnd_4403702 := by
    simpa [prefixWord, tailWord_4403702, baseEnd_4403702] using wordTrace_append hprefix tailTrace_4403702
  have hstable : (prefixWord ++ tailWord_4403702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4403702).length < 2 ^ (prefixWord ++ tailWord_4403702).sum := by decide
  have hdescent : baseEnd_4403702 < baseStart_4403702 := by decide
  rcases family_descends (prefixWord ++ tailWord_4403702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4403712 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 5, 6, 2]
def baseStart_4403712 : Nat := 118140960795 + 4403712 * 2 ^ 59
def prefixEnd_4403712 : Nat := 4983230072969 + 3 ^ 40 * 4403712 * 2
def baseEnd_4403712 : Nat := 2261220919972379690247703

theorem tailTrace_4403712 : CollatzResearch.WordTrace tailWord_4403712 prefixEnd_4403712 2261220919972379690247703 := by
  unfold tailWord_4403712
  simp only [CollatzResearch.WordTrace]
  refine ⟨80308285911055496488718695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107077714548073995318291593 80308285911055496488718695)
  ·
    refine ⟨120462428866583244733078043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80308285911055496488718695 120462428866583244733078043)
    ·
      refine ⟨180693643299874867099617065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120462428866583244733078043 180693643299874867099617065)
      ·
        refine ⟨135520232474906150324712799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180693643299874867099617065 135520232474906150324712799)
        ·
          refine ⟨203280348712359225487069199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135520232474906150324712799 203280348712359225487069199)
          ·
            refine ⟨304920523068538838230603799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203280348712359225487069199 304920523068538838230603799)
            ·
              refine ⟨457380784602808257345905699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 304920523068538838230603799 457380784602808257345905699)
              ·
                refine ⟨686071176904212386018858549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 457380784602808257345905699 686071176904212386018858549)
                ·
                  refine ⟨64319172834769911189267989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 686071176904212386018858549 64319172834769911189267989)
                  ·
                    refine ⟨3014961226629839586996937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 64319172834769911189267989 3014961226629839586996937)
                    ·
                      refine ⟨2261220919972379690247703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3014961226629839586996937 2261220919972379690247703)
                      ·
                        rfl

theorem cell23_4403712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 5, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 5, 6, 2].length) (baseStart_4403712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4403712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4403712 prefixEnd_4403712 := by exact prefixLift 4403712
  have htrace : WordTrace (prefixWord ++ tailWord_4403712) baseStart_4403712 baseEnd_4403712 := by
    simpa [prefixWord, tailWord_4403712, baseEnd_4403712] using wordTrace_append hprefix tailTrace_4403712
  have hstable : (prefixWord ++ tailWord_4403712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4403712).length < 2 ^ (prefixWord ++ tailWord_4403712).sum := by decide
  have hdescent : baseEnd_4403712 < baseStart_4403712 := by decide
  rcases family_descends (prefixWord ++ tailWord_4403712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4403715 : List Nat := [1, 1, 1, 3, 2, 1, 3, 1, 2, 3, 5]
def baseStart_4403715 : Nat := 118140960795 + 4403715 * 2 ^ 59
def prefixEnd_4403715 : Nat := 4983230072969 + 3 ^ 40 * 4403715 * 2
def baseEnd_4403715 : Nat := 2261222460414343178510189

theorem tailTrace_4403715 : CollatzResearch.WordTrace tailWord_4403715 prefixEnd_4403715 2261222460414343178510189 := by
  unfold tailWord_4403715
  simp only [CollatzResearch.WordTrace]
  refine ⟨160616681241100124489796599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107077787494066749659864399 160616681241100124489796599)
  ·
    refine ⟨240925021861650186734694899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160616681241100124489796599 240925021861650186734694899)
    ·
      refine ⟨361387532792475280102042349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240925021861650186734694899 361387532792475280102042349)
      ·
        refine ⟨135520324797178230038265881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 361387532792475280102042349 135520324797178230038265881)
        ·
          refine ⟨101640243597883672528699411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135520324797178230038265881 101640243597883672528699411)
          ·
            refine ⟨152460365396825508793049117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101640243597883672528699411 152460365396825508793049117)
            ·
              refine ⟨57172637023809565797393419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 152460365396825508793049117 57172637023809565797393419)
              ·
                refine ⟨85758955535714348696090129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57172637023809565797393419 85758955535714348696090129)
                ·
                  refine ⟨64319216651785761522067597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85758955535714348696090129 64319216651785761522067597)
                  ·
                    refine ⟨24119706244419660570775349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 64319216651785761522067597 24119706244419660570775349)
                    ·
                      refine ⟨2261222460414343178510189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24119706244419660570775349 2261222460414343178510189)
                      ·
                        rfl

theorem cell23_4403715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 3, 5].length) (baseStart_4403715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4403715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4403715 prefixEnd_4403715 := by exact prefixLift 4403715
  have htrace : WordTrace (prefixWord ++ tailWord_4403715) baseStart_4403715 baseEnd_4403715 := by
    simpa [prefixWord, tailWord_4403715, baseEnd_4403715] using wordTrace_append hprefix tailTrace_4403715
  have hstable : (prefixWord ++ tailWord_4403715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4403715).length < 2 ^ (prefixWord ++ tailWord_4403715).sum := by decide
  have hdescent : baseEnd_4403715 < baseStart_4403715 := by decide
  rcases family_descends (prefixWord ++ tailWord_4403715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4403749 : List Nat := [1, 3, 1, 2, 2, 1, 5, 1, 2, 2, 3]
def baseStart_4403749 : Nat := 118140960795 + 4403749 * 2 ^ 59
def prefixEnd_4403749 : Nat := 4983230072969 + 3 ^ 40 * 4403749 * 2
def baseEnd_4403749 : Nat := 2261239918756596045485033

theorem tailTrace_4403749 : CollatzResearch.WordTrace tailWord_4403749 prefixEnd_4403749 2261239918756596045485033 := by
  unfold tailWord_4403749
  simp only [CollatzResearch.WordTrace]
  refine ⟨160617921322976948296534301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107078614215317965531022867 160617921322976948296534301)
  ·
    refine ⟨60231720496116355611200363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160617921322976948296534301 60231720496116355611200363)
    ·
      refine ⟨90347580744174533416800545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60231720496116355611200363 90347580744174533416800545)
      ·
        refine ⟨67760685558130900062600409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90347580744174533416800545 67760685558130900062600409)
        ·
          refine ⟨50820514168598175046950307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67760685558130900062600409 50820514168598175046950307)
          ·
            refine ⟨76230771252897262570425461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50820514168598175046950307 76230771252897262570425461)
            ·
              refine ⟨7146634804959118365977387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 76230771252897262570425461 7146634804959118365977387)
              ·
                refine ⟨10719952207438677548966081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7146634804959118365977387 10719952207438677548966081)
                ·
                  refine ⟨8039964155579008161724561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10719952207438677548966081 8039964155579008161724561)
                  ·
                    refine ⟨6029973116684256121293421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8039964155579008161724561 6029973116684256121293421)
                    ·
                      refine ⟨2261239918756596045485033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6029973116684256121293421 2261239918756596045485033)
                      ·
                        rfl

theorem cell23_4403749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 1, 2, 2, 3].length) (baseStart_4403749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4403749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4403749 prefixEnd_4403749 := by exact prefixLift 4403749
  have htrace : WordTrace (prefixWord ++ tailWord_4403749) baseStart_4403749 baseEnd_4403749 := by
    simpa [prefixWord, tailWord_4403749, baseEnd_4403749] using wordTrace_append hprefix tailTrace_4403749
  have hstable : (prefixWord ++ tailWord_4403749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4403749).length < 2 ^ (prefixWord ++ tailWord_4403749).sum := by decide
  have hdescent : baseEnd_4403749 < baseStart_4403749 := by decide
  rcases family_descends (prefixWord ++ tailWord_4403749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4403755 : List Nat := [1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 6]
def baseStart_4403755 : Nat := 118140960795 + 4403755 * 2 ^ 59
def prefixEnd_4403755 : Nat := 4983230072969 + 3 ^ 40 * 4403755 * 2
def baseEnd_4403755 : Nat := 2261242999640523022010005

theorem tailTrace_4403755 : CollatzResearch.WordTrace tailWord_4403755 prefixEnd_4403755 2261242999640523022010005 := by
  unfold tailWord_4403755
  simp only [CollatzResearch.WordTrace]
  refine ⟨160618140160955211321252719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107078760107303474214168479 160618140160955211321252719)
  ·
    refine ⟨240927210241432816981879079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160618140160955211321252719 240927210241432816981879079)
    ·
      refine ⟨361390815362149225472818619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240927210241432816981879079 361390815362149225472818619)
      ·
        refine ⟨542086223043223838209227929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 361390815362149225472818619 542086223043223838209227929)
        ·
          refine ⟨406564667282417878656920947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 542086223043223838209227929 406564667282417878656920947)
          ·
            refine ⟨609847000923626817985381421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 406564667282417878656920947 609847000923626817985381421)
            ·
              refine ⟨228692625346360056744518033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 609847000923626817985381421 228692625346360056744518033)
              ·
                refine ⟨171519469009770042558388525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 228692625346360056744518033 171519469009770042558388525)
                ·
                  refine ⟨64319800878663765959395697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 171519469009770042558388525 64319800878663765959395697)
                  ·
                    refine ⟨48239850658997824469546773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 64319800878663765959395697 48239850658997824469546773)
                    ·
                      refine ⟨2261242999640523022010005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48239850658997824469546773 2261242999640523022010005)
                      ·
                        rfl

theorem cell23_4403755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 6].length) (baseStart_4403755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4403755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4403755 prefixEnd_4403755 := by exact prefixLift 4403755
  have htrace : WordTrace (prefixWord ++ tailWord_4403755) baseStart_4403755 baseEnd_4403755 := by
    simpa [prefixWord, tailWord_4403755, baseEnd_4403755] using wordTrace_append hprefix tailTrace_4403755
  have hstable : (prefixWord ++ tailWord_4403755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4403755).length < 2 ^ (prefixWord ++ tailWord_4403755).sum := by decide
  have hdescent : baseEnd_4403755 < baseStart_4403755 := by decide
  rcases family_descends (prefixWord ++ tailWord_4403755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4403772 : List Nat := [2, 2, 2, 2, 3, 1, 1, 1, 1, 2, 6]
def baseStart_4403772 : Nat := 118140960795 + 4403772 * 2 ^ 59
def prefixEnd_4403772 : Nat := 4983230072969 + 3 ^ 40 * 4403772 * 2
def baseEnd_4403772 : Nat := 2261251728811649455497427

theorem tailTrace_4403772 : CollatzResearch.WordTrace tailWord_4403772 prefixEnd_4403772 2261251728811649455497427 := by
  unfold tailWord_4403772
  simp only [CollatzResearch.WordTrace]
  refine ⟨80309380100946811612310785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107079173467929082149747713 80309380100946811612310785)
  ·
    refine ⟨60232035075710108709233089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80309380100946811612310785 60232035075710108709233089)
    ·
      refine ⟨45174026306782581531924817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60232035075710108709233089 45174026306782581531924817)
      ·
        refine ⟨33880519730086936148943613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45174026306782581531924817 33880519730086936148943613)
        ·
          refine ⟨12705194898782601055853855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33880519730086936148943613 12705194898782601055853855)
          ·
            refine ⟨19057792348173901583780783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12705194898782601055853855 19057792348173901583780783)
            ·
              refine ⟨28586688522260852375671175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19057792348173901583780783 28586688522260852375671175)
              ·
                refine ⟨42880032783391278563506763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28586688522260852375671175 42880032783391278563506763)
                ·
                  refine ⟨64320049175086917845260145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42880032783391278563506763 64320049175086917845260145)
                  ·
                    refine ⟨48240036881315188383945109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 64320049175086917845260145 48240036881315188383945109)
                    ·
                      refine ⟨2261251728811649455497427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48240036881315188383945109 2261251728811649455497427)
                      ·
                        rfl

theorem cell23_4403772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_4403772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4403772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4403772 prefixEnd_4403772 := by exact prefixLift 4403772
  have htrace : WordTrace (prefixWord ++ tailWord_4403772) baseStart_4403772 baseEnd_4403772 := by
    simpa [prefixWord, tailWord_4403772, baseEnd_4403772] using wordTrace_append hprefix tailTrace_4403772
  have hstable : (prefixWord ++ tailWord_4403772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4403772).length < 2 ^ (prefixWord ++ tailWord_4403772).sum := by decide
  have hdescent : baseEnd_4403772 < baseStart_4403772 := by decide
  rcases family_descends (prefixWord ++ tailWord_4403772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4403796 : List Nat := [2, 4, 1, 1, 1, 3, 2, 2, 3, 1, 3]
def baseStart_4403796 : Nat := 118140960795 + 4403796 * 2 ^ 59
def prefixEnd_4403796 : Nat := 4983230072969 + 3 ^ 40 * 4403796 * 2
def baseEnd_4403796 : Nat := 2261264052347357361597317

theorem tailTrace_4403796 : CollatzResearch.WordTrace tailWord_4403796 prefixEnd_4403796 2261264052347357361597317 := by
  unfold tailWord_4403796
  simp only [CollatzResearch.WordTrace]
  refine ⟨80309817776903337661747621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107079757035871116882330161 80309817776903337661747621)
  ·
    refine ⟨15058090833169375811577679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80309817776903337661747621 15058090833169375811577679)
    ·
      refine ⟨22587136249754063717366519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15058090833169375811577679 22587136249754063717366519)
      ·
        refine ⟨33880704374631095576049779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22587136249754063717366519 33880704374631095576049779)
        ·
          refine ⟨50821056561946643364074669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33880704374631095576049779 50821056561946643364074669)
          ·
            refine ⟨19057896210729991261528001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50821056561946643364074669 19057896210729991261528001)
            ·
              refine ⟨14293422158047493446146001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19057896210729991261528001 14293422158047493446146001)
              ·
                refine ⟨10720066618535620084609501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14293422158047493446146001 10720066618535620084609501)
                ·
                  refine ⟨4020024981950857531728563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10720066618535620084609501 4020024981950857531728563)
                  ·
                    refine ⟨6030037472926286297592845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4020024981950857531728563 6030037472926286297592845)
                    ·
                      refine ⟨2261264052347357361597317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6030037472926286297592845 2261264052347357361597317)
                      ·
                        rfl

theorem cell23_4403796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 2, 3, 1, 3].length) (baseStart_4403796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4403796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4403796 prefixEnd_4403796 := by exact prefixLift 4403796
  have htrace : WordTrace (prefixWord ++ tailWord_4403796) baseStart_4403796 baseEnd_4403796 := by
    simpa [prefixWord, tailWord_4403796, baseEnd_4403796] using wordTrace_append hprefix tailTrace_4403796
  have hstable : (prefixWord ++ tailWord_4403796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4403796).length < 2 ^ (prefixWord ++ tailWord_4403796).sum := by decide
  have hdescent : baseEnd_4403796 < baseStart_4403796 := by decide
  rcases family_descends (prefixWord ++ tailWord_4403796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4403799 : List Nat := [1, 1, 3, 2, 2, 2, 4, 2, 1, 5]
def baseStart_4403799 : Nat := 118140960795 + 4403799 * 2 ^ 59
def prefixEnd_4403799 : Nat := 4983230072969 + 3 ^ 40 * 4403799 * 2
def baseEnd_4403799 : Nat := 753755197596440283286601

theorem tailTrace_4403799 : CollatzResearch.WordTrace tailWord_4403799 prefixEnd_4403799 753755197596440283286601 := by
  unfold tailWord_4403799
  simp only [CollatzResearch.WordTrace]
  refine ⟨160619744972795806835854451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107079829981863871223902967 160619744972795806835854451)
  ·
    refine ⟨240929617459193710253781677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160619744972795806835854451 240929617459193710253781677)
    ·
      refine ⟨90348606547197641345168129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 240929617459193710253781677 90348606547197641345168129)
      ·
        refine ⟨67761454910398231008876097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90348606547197641345168129 67761454910398231008876097)
        ·
          refine ⟨50821091182798673256657073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67761454910398231008876097 50821091182798673256657073)
          ·
            refine ⟨38115818387099004942492805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50821091182798673256657073 38115818387099004942492805)
            ·
              refine ⟨7146715947581063426717401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38115818387099004942492805 7146715947581063426717401)
              ·
                refine ⟨5360036960685797570038051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7146715947581063426717401 5360036960685797570038051)
                ·
                  refine ⟨8040055441028696355057077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5360036960685797570038051 8040055441028696355057077)
                  ·
                    refine ⟨753755197596440283286601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8040055441028696355057077 753755197596440283286601)
                    ·
                      rfl

theorem cell23_4403799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 2, 1, 5].length) (baseStart_4403799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4403799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4403799 prefixEnd_4403799 := by exact prefixLift 4403799
  have htrace : WordTrace (prefixWord ++ tailWord_4403799) baseStart_4403799 baseEnd_4403799 := by
    simpa [prefixWord, tailWord_4403799, baseEnd_4403799] using wordTrace_append hprefix tailTrace_4403799
  have hstable : (prefixWord ++ tailWord_4403799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4403799).length < 2 ^ (prefixWord ++ tailWord_4403799).sum := by decide
  have hdescent : baseEnd_4403799 < baseStart_4403799 := by decide
  rcases family_descends (prefixWord ++ tailWord_4403799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4403812 : List Nat := [2, 3, 1, 1, 2, 2, 2, 1, 3, 6]
def baseStart_4403812 : Nat := 118140960795 + 4403812 * 2 ^ 59
def prefixEnd_4403812 : Nat := 4983230072969 + 3 ^ 40 * 4403812 * 2
def baseEnd_4403812 : Nat := 753757422679276432999081

theorem tailTrace_4403812 : CollatzResearch.WordTrace tailWord_4403812 prefixEnd_4403812 753757422679276432999081 := by
  unfold tailWord_4403812
  simp only [CollatzResearch.WordTrace]
  refine ⟨80310109560874355028038845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107080146081165806704051793 80310109560874355028038845)
  ·
    refine ⟨30116291085327883135514567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80310109560874355028038845 30116291085327883135514567)
    ·
      refine ⟨45174436627991824703271851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30116291085327883135514567 45174436627991824703271851)
      ·
        refine ⟨67761654941987737054907777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45174436627991824703271851 67761654941987737054907777)
        ·
          refine ⟨50821241206490802791180833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67761654941987737054907777 50821241206490802791180833)
          ·
            refine ⟨38115930904868102093385625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50821241206490802791180833 38115930904868102093385625)
            ·
              refine ⟨28586948178651076570039219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38115930904868102093385625 28586948178651076570039219)
              ·
                refine ⟨42880422267976614855058829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28586948178651076570039219 42880422267976614855058829)
                ·
                  refine ⟨16080158350491230570647061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42880422267976614855058829 16080158350491230570647061)
                  ·
                    refine ⟨753757422679276432999081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16080158350491230570647061 753757422679276432999081)
                    ·
                      rfl

theorem cell23_4403812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 3, 6].length) (baseStart_4403812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4403812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4403812 prefixEnd_4403812 := by exact prefixLift 4403812
  have htrace : WordTrace (prefixWord ++ tailWord_4403812) baseStart_4403812 baseEnd_4403812 := by
    simpa [prefixWord, tailWord_4403812, baseEnd_4403812] using wordTrace_append hprefix tailTrace_4403812
  have hstable : (prefixWord ++ tailWord_4403812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4403812).length < 2 ^ (prefixWord ++ tailWord_4403812).sum := by decide
  have hdescent : baseEnd_4403812 < baseStart_4403812 := by decide
  rcases family_descends (prefixWord ++ tailWord_4403812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4403830 : List Nat := [5, 1, 1, 2, 3, 2, 1, 1, 3, 1, 3]
def baseStart_4403830 : Nat := 118140960795 + 4403830 * 2 ^ 59
def prefixEnd_4403830 : Nat := 4983230072969 + 3 ^ 40 * 4403830 * 2
def baseEnd_4403830 : Nat := 2261281510689610228572161

theorem tailTrace_4403830 : CollatzResearch.WordTrace tailWord_4403830 prefixEnd_4403830 2261281510689610228572161 := by
  unfold tailWord_4403830
  simp only [CollatzResearch.WordTrace]
  refine ⟨10038804727230218695639559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 107080583757122332753488629 10038804727230218695639559)
  ·
    refine ⟨15058207090845328043459339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10038804727230218695639559 15058207090845328043459339)
    ·
      refine ⟨22587310636267992065189009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15058207090845328043459339 22587310636267992065189009)
      ·
        refine ⟨16940482977200994048891757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22587310636267992065189009 16940482977200994048891757)
        ·
          refine ⟨6352681116450372768334409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16940482977200994048891757 6352681116450372768334409)
          ·
            refine ⟨4764510837337779576250807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6352681116450372768334409 4764510837337779576250807)
            ·
              refine ⟨7146766256006669364376211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4764510837337779576250807 7146766256006669364376211)
              ·
                refine ⟨10720149384010004046564317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7146766256006669364376211 10720149384010004046564317)
                ·
                  refine ⟨4020056019003751517461619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10720149384010004046564317 4020056019003751517461619)
                  ·
                    refine ⟨6030084028505627276192429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4020056019003751517461619 6030084028505627276192429)
                    ·
                      refine ⟨2261281510689610228572161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6030084028505627276192429 2261281510689610228572161)
                      ·
                        rfl

theorem cell23_4403830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_4403830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4403830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4403830 prefixEnd_4403830 := by exact prefixLift 4403830
  have htrace : WordTrace (prefixWord ++ tailWord_4403830) baseStart_4403830 baseEnd_4403830 := by
    simpa [prefixWord, tailWord_4403830, baseEnd_4403830] using wordTrace_append hprefix tailTrace_4403830
  have hstable : (prefixWord ++ tailWord_4403830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4403830).length < 2 ^ (prefixWord ++ tailWord_4403830).sum := by decide
  have hdescent : baseEnd_4403830 < baseStart_4403830 := by decide
  rcases family_descends (prefixWord ++ tailWord_4403830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4403832 : List Nat := [2, 1, 2, 1, 1, 1, 2, 4, 3, 2, 4]
def baseStart_4403832 : Nat := 118140960795 + 4403832 * 2 ^ 59
def prefixEnd_4403832 : Nat := 4983230072969 + 3 ^ 40 * 4403832 * 2
def baseEnd_4403832 : Nat := 2261282537650919220747151

theorem tailTrace_4403832 : CollatzResearch.WordTrace tailWord_4403832 prefixEnd_4403832 2261282537650919220747151 := by
  unfold tailWord_4403832
  simp only [CollatzResearch.WordTrace]
  refine ⟨80310474290838126735902875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107080632387784168981203833 80310474290838126735902875)
  ·
    refine ⟨120465711436257190103854313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80310474290838126735902875 120465711436257190103854313)
    ·
      refine ⟨90349283577192892577890735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120465711436257190103854313 90349283577192892577890735)
      ·
        refine ⟨135523925365789338866836103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90349283577192892577890735 135523925365789338866836103)
        ·
          refine ⟨203285888048684008300254155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135523925365789338866836103 203285888048684008300254155)
          ·
            refine ⟨304928832073026012450381233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203285888048684008300254155 304928832073026012450381233)
            ·
              refine ⟨228696624054769509337785925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 304928832073026012450381233 228696624054769509337785925)
              ·
                refine ⟨42880617010269283000834861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 228696624054769509337785925 42880617010269283000834861)
                ·
                  refine ⟨16080231378850981125313073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42880617010269283000834861 16080231378850981125313073)
                  ·
                    refine ⟨12060173534138235843984805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16080231378850981125313073 12060173534138235843984805)
                    ·
                      refine ⟨2261282537650919220747151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12060173534138235843984805 2261282537650919220747151)
                      ·
                        rfl

theorem cell23_4403832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 3, 2, 4].length) (baseStart_4403832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4403832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4403832 prefixEnd_4403832 := by exact prefixLift 4403832
  have htrace : WordTrace (prefixWord ++ tailWord_4403832) baseStart_4403832 baseEnd_4403832 := by
    simpa [prefixWord, tailWord_4403832, baseEnd_4403832] using wordTrace_append hprefix tailTrace_4403832
  have hstable : (prefixWord ++ tailWord_4403832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4403832).length < 2 ^ (prefixWord ++ tailWord_4403832).sum := by decide
  have hdescent : baseEnd_4403832 < baseStart_4403832 := by decide
  rcases family_descends (prefixWord ++ tailWord_4403832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4403869 : List Nat := [1, 4, 2, 1, 1, 1, 3, 1, 3, 3, 3]
def baseStart_4403869 : Nat := 118140960795 + 4403869 * 2 ^ 59
def prefixEnd_4403869 : Nat := 4983230072969 + 3 ^ 40 * 4403869 * 2
def baseEnd_4403869 : Nat := 2261301536435135575984481

theorem tailTrace_4403869 : CollatzResearch.WordTrace tailWord_4403869 prefixEnd_4403869 2261301536435135575984481 := by
  unfold tailWord_4403869
  simp only [CollatzResearch.WordTrace]
  refine ⟨160622298082542208790902661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107081532055028139193935107 160622298082542208790902661)
  ·
    refine ⟨30116680890476664148294249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 160622298082542208790902661 30116680890476664148294249)
    ·
      refine ⟨22587510667857498111220687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30116680890476664148294249 22587510667857498111220687)
      ·
        refine ⟨33881266001786247166831031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22587510667857498111220687 33881266001786247166831031)
        ·
          refine ⟨50821899002679370750246547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33881266001786247166831031 50821899002679370750246547)
          ·
            refine ⟨76232848504019056125369821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50821899002679370750246547 76232848504019056125369821)
            ·
              refine ⟨28587318189007146047013683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76232848504019056125369821 28587318189007146047013683)
              ·
                refine ⟨42880977283510719070520525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28587318189007146047013683 42880977283510719070520525)
                ·
                  refine ⟨16080366481316519651445197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42880977283510719070520525 16080366481316519651445197)
                  ·
                    refine ⟨6030137430493694869291949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16080366481316519651445197 6030137430493694869291949)
                    ·
                      refine ⟨2261301536435135575984481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6030137430493694869291949 2261301536435135575984481)
                      ·
                        rfl

theorem cell23_4403869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 3, 3, 3].length) (baseStart_4403869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4403869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4403869 prefixEnd_4403869 := by exact prefixLift 4403869
  have htrace : WordTrace (prefixWord ++ tailWord_4403869) baseStart_4403869 baseEnd_4403869 := by
    simpa [prefixWord, tailWord_4403869, baseEnd_4403869] using wordTrace_append hprefix tailTrace_4403869
  have hstable : (prefixWord ++ tailWord_4403869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4403869).length < 2 ^ (prefixWord ++ tailWord_4403869).sum := by decide
  have hdescent : baseEnd_4403869 < baseStart_4403869 := by decide
  rcases family_descends (prefixWord ++ tailWord_4403869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4403873 : List Nat := [1, 2, 3, 3, 4, 1, 1, 1, 1, 1, 5]
def baseStart_4403873 : Nat := 118140960795 + 4403873 * 2 ^ 59
def prefixEnd_4403873 : Nat := 4983230072969 + 3 ^ 40 * 4403873 * 2
def baseEnd_4403873 : Nat := 2261303590357753560334463

theorem tailTrace_4403873 : CollatzResearch.WordTrace tailWord_4403873 prefixEnd_4403873 2261303590357753560334463 := by
  unfold tailWord_4403873
  simp only [CollatzResearch.WordTrace]
  refine ⟨160622443974527717474048273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107081629316351811649365515 160622443974527717474048273)
  ·
    refine ⟨120466832980895788105536205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160622443974527717474048273 120466832980895788105536205)
    ·
      refine ⟨45175062367835920539576077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120466832980895788105536205 45175062367835920539576077)
      ·
        refine ⟨16940648387938470202341029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45175062367835920539576077 16940648387938470202341029)
        ·
          refine ⟨3176371572738463162938943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16940648387938470202341029 3176371572738463162938943)
          ·
            refine ⟨4764557359107694744408415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3176371572738463162938943 4764557359107694744408415)
            ·
              refine ⟨7146836038661542116612623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4764557359107694744408415 7146836038661542116612623)
              ·
                refine ⟨10720254057992313174918935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7146836038661542116612623 10720254057992313174918935)
                ·
                  refine ⟨16080381086988469762378403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10720254057992313174918935 16080381086988469762378403)
                  ·
                    refine ⟨24120571630482704643567605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16080381086988469762378403 24120571630482704643567605)
                    ·
                      refine ⟨2261303590357753560334463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24120571630482704643567605 2261303590357753560334463)
                      ·
                        rfl

theorem cell23_4403873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 1, 1, 1, 5].length) (baseStart_4403873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4403873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4403873 prefixEnd_4403873 := by exact prefixLift 4403873
  have htrace : WordTrace (prefixWord ++ tailWord_4403873) baseStart_4403873 baseEnd_4403873 := by
    simpa [prefixWord, tailWord_4403873, baseEnd_4403873] using wordTrace_append hprefix tailTrace_4403873
  have hstable : (prefixWord ++ tailWord_4403873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4403873).length < 2 ^ (prefixWord ++ tailWord_4403873).sum := by decide
  have hdescent : baseEnd_4403873 < baseStart_4403873 := by decide
  rcases family_descends (prefixWord ++ tailWord_4403873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4403887 : List Nat := [1, 1, 2, 1, 2, 7, 2, 2, 1, 2, 2]
def baseStart_4403887 : Nat := 118140960795 + 4403887 * 2 ^ 59
def prefixEnd_4403887 : Nat := 4983230072969 + 3 ^ 40 * 4403887 * 2
def baseEnd_4403887 : Nat := 2261310779086916505559399

theorem tailTrace_4403887 : CollatzResearch.WordTrace tailWord_4403887 prefixEnd_4403887 2261310779086916505559399 := by
  unfold tailWord_4403887
  simp only [CollatzResearch.WordTrace]
  refine ⟨160622954596476997865057915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107081969730984665243371943 160622954596476997865057915)
  ·
    refine ⟨240934431894715496797586873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160622954596476997865057915 240934431894715496797586873)
    ·
      refine ⟨180700823921036622598190155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 240934431894715496797586873 180700823921036622598190155)
      ·
        refine ⟨271051235881554933897285233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180700823921036622598190155 271051235881554933897285233)
        ·
          refine ⟨203288426911166200422963925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 271051235881554933897285233 203288426911166200422963925)
          ·
            refine ⟨4764572505730457822413217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 203288426911166200422963925 4764572505730457822413217)
            ·
              refine ⟨3573429379297843366809913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4764572505730457822413217 3573429379297843366809913)
              ·
                refine ⟨2680072034473382525107435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3573429379297843366809913 2680072034473382525107435)
                ·
                  refine ⟨4020108051710073787661153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2680072034473382525107435 4020108051710073787661153)
                  ·
                    refine ⟨3015081038782555340745865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4020108051710073787661153 3015081038782555340745865)
                    ·
                      refine ⟨2261310779086916505559399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3015081038782555340745865 2261310779086916505559399)
                      ·
                        rfl

theorem cell23_4403887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 2, 2, 1, 2, 2].length) (baseStart_4403887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4403887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4403887 prefixEnd_4403887 := by exact prefixLift 4403887
  have htrace : WordTrace (prefixWord ++ tailWord_4403887) baseStart_4403887 baseEnd_4403887 := by
    simpa [prefixWord, tailWord_4403887, baseEnd_4403887] using wordTrace_append hprefix tailTrace_4403887
  have hstable : (prefixWord ++ tailWord_4403887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4403887).length < 2 ^ (prefixWord ++ tailWord_4403887).sum := by decide
  have hdescent : baseEnd_4403887 < baseStart_4403887 := by decide
  rcases family_descends (prefixWord ++ tailWord_4403887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4403910 : List Nat := [6, 1, 2, 1, 2, 1, 3, 7]
def baseStart_4403910 : Nat := 118140960795 + 4403910 * 2 ^ 59
def prefixEnd_4403910 : Nat := 4983230072969 + 3 ^ 40 * 4403910 * 2
def baseEnd_4403910 : Nat := 83752688486739626502659

theorem tailTrace_4403910 : CollatzResearch.WordTrace tailWord_4403910 prefixEnd_4403910 83752688486739626502659 := by
  unfold tailWord_4403910
  simp only [CollatzResearch.WordTrace]
  refine ⟨5019493546106052274785787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 107082528983595781862096789 5019493546106052274785787)
  ·
    refine ⟨7529240319159078412178681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5019493546106052274785787 7529240319159078412178681)
    ·
      refine ⟨5646930239369308809134011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7529240319159078412178681 5646930239369308809134011)
      ·
        refine ⟨8470395359053963213701017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5646930239369308809134011 8470395359053963213701017)
        ·
          refine ⟨6352796519290472410275763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8470395359053963213701017 6352796519290472410275763)
          ·
            refine ⟨9529194778935708615413645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6352796519290472410275763 9529194778935708615413645)
            ·
              refine ⟨3573448042100890730780117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9529194778935708615413645 3573448042100890730780117)
              ·
                refine ⟨83752688486739626502659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3573448042100890730780117 83752688486739626502659)
                ·
                  rfl

theorem cell23_4403910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 3, 7].length) (baseStart_4403910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4403910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4403910 prefixEnd_4403910 := by exact prefixLift 4403910
  have htrace : WordTrace (prefixWord ++ tailWord_4403910) baseStart_4403910 baseEnd_4403910 := by
    simpa [prefixWord, tailWord_4403910, baseEnd_4403910] using wordTrace_append hprefix tailTrace_4403910
  have hstable : (prefixWord ++ tailWord_4403910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4403910).length < 2 ^ (prefixWord ++ tailWord_4403910).sum := by decide
  have hdescent : baseEnd_4403910 < baseStart_4403910 := by decide
  rcases family_descends (prefixWord ++ tailWord_4403910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4403960 : List Nat := [2, 1, 2, 1, 1, 2, 7, 1, 2, 2, 2]
def baseStart_4403960 : Nat := 118140960795 + 4403960 * 2 ^ 59
def prefixEnd_4403960 : Nat := 4983230072969 + 3 ^ 40 * 4403960 * 2
def baseEnd_4403960 : Nat := 2261348263174694719946563

theorem tailTrace_4403960 : CollatzResearch.WordTrace tailWord_4403960 prefixEnd_4403960 2261348263174694719946563 := by
  unfold tailWord_4403960
  simp only [CollatzResearch.WordTrace]
  refine ⟨80312808562606265666232667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107083744750141687554976889 80312808562606265666232667)
  ·
    refine ⟨120469212843909398499349001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80312808562606265666232667 120469212843909398499349001)
    ·
      refine ⟨90351909632932048874511751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120469212843909398499349001 90351909632932048874511751)
      ·
        refine ⟨135527864449398073311767627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90351909632932048874511751 135527864449398073311767627)
        ·
          refine ⟨203291796674097109967651441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135527864449398073311767627 203291796674097109967651441)
          ·
            refine ⟨152468847505572832475738581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 203291796674097109967651441 152468847505572832475738581)
            ·
              refine ⟨3573488613411863261150123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 152468847505572832475738581 3573488613411863261150123)
              ·
                refine ⟨5360232920117794891725185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3573488613411863261150123 5360232920117794891725185)
                ·
                  refine ⟨4020174690088346168793889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5360232920117794891725185 4020174690088346168793889)
                  ·
                    refine ⟨3015131017566259626595417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4020174690088346168793889 3015131017566259626595417)
                    ·
                      refine ⟨2261348263174694719946563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3015131017566259626595417 2261348263174694719946563)
                      ·
                        rfl

theorem cell23_4403960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 7, 1, 2, 2, 2].length) (baseStart_4403960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4403960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4403960 prefixEnd_4403960 := by exact prefixLift 4403960
  have htrace : WordTrace (prefixWord ++ tailWord_4403960) baseStart_4403960 baseEnd_4403960 := by
    simpa [prefixWord, tailWord_4403960, baseEnd_4403960] using wordTrace_append hprefix tailTrace_4403960
  have hstable : (prefixWord ++ tailWord_4403960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4403960).length < 2 ^ (prefixWord ++ tailWord_4403960).sum := by decide
  have hdescent : baseEnd_4403960 < baseStart_4403960 := by decide
  rcases family_descends (prefixWord ++ tailWord_4403960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4403966 : List Nat := [4, 2, 2, 1, 2, 1, 2, 2, 7]
def baseStart_4403966 : Nat := 118140960795 + 4403966 * 2 ^ 59
def prefixEnd_4403966 : Nat := 4983230072969 + 3 ^ 40 * 4403966 * 2
def baseEnd_4403966 : Nat := 251261260450957966274615

theorem tailTrace_4403966 : CollatzResearch.WordTrace tailWord_4403966 prefixEnd_4403966 251261260450957966274615 := by
  unfold tailWord_4403966
  simp only [CollatzResearch.WordTrace]
  refine ⟨20078229495398849294647969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107083890642127196238122501 20078229495398849294647969)
  ·
    refine ⟨15058672121549136970985977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20078229495398849294647969 15058672121549136970985977)
    ·
      refine ⟨11294004091161852728239483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15058672121549136970985977 11294004091161852728239483)
      ·
        refine ⟨16941006136742779092359225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11294004091161852728239483 16941006136742779092359225)
        ·
          refine ⟨12705754602557084319269419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16941006136742779092359225 12705754602557084319269419)
          ·
            refine ⟨19058631903835626478904129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12705754602557084319269419 19058631903835626478904129)
            ·
              refine ⟨14293973927876719859178097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19058631903835626478904129 14293973927876719859178097)
              ·
                refine ⟨10720480445907539894383573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14293973927876719859178097 10720480445907539894383573)
                ·
                  refine ⟨251261260450957966274615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10720480445907539894383573 251261260450957966274615)
                  ·
                    rfl

theorem cell23_4403966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 2, 7].length) (baseStart_4403966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4403966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4403966 prefixEnd_4403966 := by exact prefixLift 4403966
  have htrace : WordTrace (prefixWord ++ tailWord_4403966) baseStart_4403966 baseEnd_4403966 := by
    simpa [prefixWord, tailWord_4403966, baseEnd_4403966] using wordTrace_append hprefix tailTrace_4403966
  have hstable : (prefixWord ++ tailWord_4403966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4403966).length < 2 ^ (prefixWord ++ tailWord_4403966).sum := by decide
  have hdescent : baseEnd_4403966 < baseStart_4403966 := by decide
  rcases family_descends (prefixWord ++ tailWord_4403966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4403979 : List Nat := [1, 1, 1, 1, 5, 1, 1, 5, 2, 5]
def baseStart_4403979 : Nat := 118140960795 + 4403979 * 2 ^ 59
def prefixEnd_4403979 : Nat := 4983230072969 + 3 ^ 40 * 4403979 * 2
def baseEnd_4403979 : Nat := 753786006435710048536325

theorem tailTrace_4403979 : CollatzResearch.WordTrace tailWord_4403979 prefixEnd_4403979 753786006435710048536325 := by
  unfold tailWord_4403979
  simp only [CollatzResearch.WordTrace]
  refine ⟨160626310112143697577406991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107084206741429131718271327 160626310112143697577406991)
  ·
    refine ⟨240939465168215546366110487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160626310112143697577406991 240939465168215546366110487)
    ·
      refine ⟨361409197752323319549165731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240939465168215546366110487 361409197752323319549165731)
      ·
        refine ⟨542113796628484979323748597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 361409197752323319549165731 542113796628484979323748597)
        ·
          refine ⟨50823168433920466811601431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 542113796628484979323748597 50823168433920466811601431)
          ·
            refine ⟨76234752650880700217402147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50823168433920466811601431 76234752650880700217402147)
            ·
              refine ⟨114352128976321050326103221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76234752650880700217402147 114352128976321050326103221)
              ·
                refine ⟨10720512091530098468072177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 114352128976321050326103221 10720512091530098468072177)
                ·
                  refine ⟨8040384068647573851054133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10720512091530098468072177 8040384068647573851054133)
                  ·
                    refine ⟨753786006435710048536325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8040384068647573851054133 753786006435710048536325)
                    ·
                      rfl

theorem cell23_4403979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 5, 2, 5].length) (baseStart_4403979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4403979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4403979 prefixEnd_4403979 := by exact prefixLift 4403979
  have htrace : WordTrace (prefixWord ++ tailWord_4403979) baseStart_4403979 baseEnd_4403979 := by
    simpa [prefixWord, tailWord_4403979, baseEnd_4403979] using wordTrace_append hprefix tailTrace_4403979
  have hstable : (prefixWord ++ tailWord_4403979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4403979).length < 2 ^ (prefixWord ++ tailWord_4403979).sum := by decide
  have hdescent : baseEnd_4403979 < baseStart_4403979 := by decide
  rcases family_descends (prefixWord ++ tailWord_4403979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4403989 : List Nat := [1, 3, 2, 1, 2, 2, 2, 2, 1, 2, 5]
def baseStart_4403989 : Nat := 118140960795 + 4403989 * 2 ^ 59
def prefixEnd_4403989 : Nat := 4983230072969 + 3 ^ 40 * 4403989 * 2
def baseEnd_4403989 : Nat := 2261363154113675106483929

theorem tailTrace_4403989 : CollatzResearch.WordTrace tailWord_4403989 prefixEnd_4403989 2261363154113675106483929 := by
  unfold tailWord_4403989
  simp only [CollatzResearch.WordTrace]
  refine ⟨160626674842107469285271021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107084449894738312856847347 160626674842107469285271021)
  ·
    refine ⟨60235003065790300981976633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160626674842107469285271021 60235003065790300981976633)
    ·
      refine ⟨45176252299342725736482475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60235003065790300981976633 45176252299342725736482475)
      ·
        refine ⟨67764378449014088604723713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45176252299342725736482475 67764378449014088604723713)
        ·
          refine ⟨50823283836760566453542785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67764378449014088604723713 50823283836760566453542785)
          ·
            refine ⟨38117462877570424840157089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50823283836760566453542785 38117462877570424840157089)
            ·
              refine ⟨28588097158177818630117817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38117462877570424840157089 28588097158177818630117817)
              ·
                refine ⟨21441072868633363972588363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28588097158177818630117817 21441072868633363972588363)
                ·
                  refine ⟨32161609302950045958882545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21441072868633363972588363 32161609302950045958882545)
                  ·
                    refine ⟨24121206977212534469161909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32161609302950045958882545 24121206977212534469161909)
                    ·
                      refine ⟨2261363154113675106483929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24121206977212534469161909 2261363154113675106483929)
                      ·
                        rfl

theorem cell23_4403989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 2, 5].length) (baseStart_4403989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4403989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4403989 prefixEnd_4403989 := by exact prefixLift 4403989
  have htrace : WordTrace (prefixWord ++ tailWord_4403989) baseStart_4403989 baseEnd_4403989 := by
    simpa [prefixWord, tailWord_4403989, baseEnd_4403989] using wordTrace_append hprefix tailTrace_4403989
  have hstable : (prefixWord ++ tailWord_4403989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4403989).length < 2 ^ (prefixWord ++ tailWord_4403989).sum := by decide
  have hdescent : baseEnd_4403989 < baseStart_4403989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4403989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4403996 : List Nat := [2, 2, 3, 1, 1, 4, 1, 2, 2, 5]
def baseStart_4403996 : Nat := 118140960795 + 4403996 * 2 ^ 59
def prefixEnd_4403996 : Nat := 4983230072969 + 3 ^ 40 * 4403996 * 2
def baseEnd_4403996 : Nat := 753788916159418859698799

theorem tailTrace_4403996 : CollatzResearch.WordTrace tailWord_4403996 prefixEnd_4403996 753788916159418859698799 := by
  unfold tailWord_4403996
  simp only [CollatzResearch.WordTrace]
  refine ⟨80313465076541054740387921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107084620102054739653850561 80313465076541054740387921)
  ·
    refine ⟨60235098807405791055290941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80313465076541054740387921 60235098807405791055290941)
    ·
      refine ⟨22588162052777171645734103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60235098807405791055290941 22588162052777171645734103)
      ·
        refine ⟨33882243079165757468601155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22588162052777171645734103 33882243079165757468601155)
        ·
          refine ⟨50823364618748636202901733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33882243079165757468601155 50823364618748636202901733)
          ·
            refine ⟨9529380866015369288044075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50823364618748636202901733 9529380866015369288044075)
            ·
              refine ⟨14294071299023053932066113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9529380866015369288044075 14294071299023053932066113)
              ·
                refine ⟨10720553474267290449049585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14294071299023053932066113 10720553474267290449049585)
                ·
                  refine ⟨8040415105700467836787189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10720553474267290449049585 8040415105700467836787189)
                  ·
                    refine ⟨753788916159418859698799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8040415105700467836787189 753788916159418859698799)
                    ·
                      rfl

theorem cell23_4403996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_4403996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4403996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4403996 prefixEnd_4403996 := by exact prefixLift 4403996
  have htrace : WordTrace (prefixWord ++ tailWord_4403996) baseStart_4403996 baseEnd_4403996 := by
    simpa [prefixWord, tailWord_4403996, baseEnd_4403996] using wordTrace_append hprefix tailTrace_4403996
  have hstable : (prefixWord ++ tailWord_4403996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4403996).length < 2 ^ (prefixWord ++ tailWord_4403996).sum := by decide
  have hdescent : baseEnd_4403996 < baseStart_4403996 := by decide
  rcases family_descends (prefixWord ++ tailWord_4403996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4404016 : List Nat := [2, 1, 1, 1, 2, 2, 1, 5, 2, 4, 2]
def baseStart_4404016 : Nat := 118140960795 + 4404016 * 2 ^ 59
def prefixEnd_4404016 : Nat := 4983230072969 + 3 ^ 40 * 4404016 * 2
def baseEnd_4404016 : Nat := 2261377018091346500846305

theorem tailTrace_4404016 : CollatzResearch.WordTrace tailWord_4404016 prefixEnd_4404016 2261377018091346500846305 := by
  unfold tailWord_4404016
  simp only [CollatzResearch.WordTrace]
  refine ⟨80313829806504826448251951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107085106408673101931002601 80313829806504826448251951)
  ·
    refine ⟨120470744709757239672377927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80313829806504826448251951 120470744709757239672377927)
    ·
      refine ⟨180706117064635859508566891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120470744709757239672377927 180706117064635859508566891)
      ·
        refine ⟨271059175596953789262850337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180706117064635859508566891 271059175596953789262850337)
        ·
          refine ⟨203294381697715341947137753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 271059175596953789262850337 203294381697715341947137753)
          ·
            refine ⟨152470786273286506460353315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 203294381697715341947137753 152470786273286506460353315)
            ·
              refine ⟨228706179409929759690529973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152470786273286506460353315 228706179409929759690529973)
              ·
                refine ⟨21441204319680914970987185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 228706179409929759690529973 21441204319680914970987185)
                ·
                  refine ⟨16080903239760686228240389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21441204319680914970987185 16080903239760686228240389)
                  ·
                    refine ⟨3015169357455128667795073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16080903239760686228240389 3015169357455128667795073)
                    ·
                      refine ⟨2261377018091346500846305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3015169357455128667795073 2261377018091346500846305)
                      ·
                        rfl

theorem cell23_4404016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 2, 4, 2].length) (baseStart_4404016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4404016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4404016 prefixEnd_4404016 := by exact prefixLift 4404016
  have htrace : WordTrace (prefixWord ++ tailWord_4404016) baseStart_4404016 baseEnd_4404016 := by
    simpa [prefixWord, tailWord_4404016, baseEnd_4404016] using wordTrace_append hprefix tailTrace_4404016
  have hstable : (prefixWord ++ tailWord_4404016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4404016).length < 2 ^ (prefixWord ++ tailWord_4404016).sum := by decide
  have hdescent : baseEnd_4404016 < baseStart_4404016 := by decide
  rcases family_descends (prefixWord ++ tailWord_4404016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4404094 : List Nat := [4, 2, 3, 1, 2, 1, 2, 3, 1, 4]
def baseStart_4404094 : Nat := 118140960795 + 4404094 * 2 ^ 59
def prefixEnd_4404094 : Nat := 4983230072969 + 3 ^ 40 * 4404094 * 2
def baseEnd_4404094 : Nat := 753805689860799065223649

theorem tailTrace_4404094 : CollatzResearch.WordTrace tailWord_4404094 prefixEnd_4404094 753805689860799065223649 := by
  unfold tailWord_4404094
  simp only [CollatzResearch.WordTrace]
  refine ⟨20078813063340884027230417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107087003004484714811895557 20078813063340884027230417)
  ·
    refine ⟨15059109797505663020422813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20078813063340884027230417 15059109797505663020422813)
    ·
      refine ⟨5647166174064623632658555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15059109797505663020422813 5647166174064623632658555)
      ·
        refine ⟨8470749261096935448987833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5647166174064623632658555 8470749261096935448987833)
        ·
          refine ⟨6353061945822701586740875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8470749261096935448987833 6353061945822701586740875)
          ·
            refine ⟨9529592918734052380111313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6353061945822701586740875 9529592918734052380111313)
            ·
              refine ⟨7147194689050539285083485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9529592918734052380111313 7147194689050539285083485)
              ·
                refine ⟨2680198008393952231906307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7147194689050539285083485 2680198008393952231906307)
                ·
                  refine ⟨4020297012590928347859461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2680198008393952231906307 4020297012590928347859461)
                  ·
                    refine ⟨753805689860799065223649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4020297012590928347859461 753805689860799065223649)
                    ·
                      rfl

theorem cell23_4404094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_4404094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4404094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4404094 prefixEnd_4404094 := by exact prefixLift 4404094
  have htrace : WordTrace (prefixWord ++ tailWord_4404094) baseStart_4404094 baseEnd_4404094 := by
    simpa [prefixWord, tailWord_4404094, baseEnd_4404094] using wordTrace_append hprefix tailTrace_4404094
  have hstable : (prefixWord ++ tailWord_4404094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4404094).length < 2 ^ (prefixWord ++ tailWord_4404094).sum := by decide
  have hdescent : baseEnd_4404094 < baseStart_4404094 := by decide
  rcases family_descends (prefixWord ++ tailWord_4404094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4404103 : List Nat := [1, 1, 4, 2, 3, 2, 1, 3, 1, 5]
def baseStart_4404103 : Nat := 118140960795 + 4404103 * 2 ^ 59
def prefixEnd_4404103 : Nat := 4983230072969 + 3 ^ 40 * 4404103 * 2
def baseEnd_4404103 : Nat := 753807230302762553486135

theorem tailTrace_4404103 : CollatzResearch.WordTrace tailWord_4404103 prefixEnd_4404103 753807230302762553486135 := by
  unfold tailWord_4404103
  simp only [CollatzResearch.WordTrace]
  refine ⟨160630832763694466754920963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107087221842462977836613975 160630832763694466754920963)
  ·
    refine ⟨240946249145541700132381445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160630832763694466754920963 240946249145541700132381445)
    ·
      refine ⟨45177421714789068774821521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 240946249145541700132381445 45177421714789068774821521)
      ·
        refine ⟨33883066286091801581116141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45177421714789068774821521 33883066286091801581116141)
        ·
          refine ⟨12706149857284425592918553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33883066286091801581116141 12706149857284425592918553)
          ·
            refine ⟨9529612392963319194688915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12706149857284425592918553 9529612392963319194688915)
            ·
              refine ⟨14294418589444978792033373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9529612392963319194688915 14294418589444978792033373)
              ·
                refine ⟨5360406971041867047012515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14294418589444978792033373 5360406971041867047012515)
                ·
                  refine ⟨8040610456562800570518773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5360406971041867047012515 8040610456562800570518773)
                  ·
                    refine ⟨753807230302762553486135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8040610456562800570518773 753807230302762553486135)
                    ·
                      rfl

theorem cell23_4404103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 3, 1, 5].length) (baseStart_4404103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4404103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4404103 prefixEnd_4404103 := by exact prefixLift 4404103
  have htrace : WordTrace (prefixWord ++ tailWord_4404103) baseStart_4404103 baseEnd_4404103 := by
    simpa [prefixWord, tailWord_4404103, baseEnd_4404103] using wordTrace_append hprefix tailTrace_4404103
  have hstable : (prefixWord ++ tailWord_4404103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4404103).length < 2 ^ (prefixWord ++ tailWord_4404103).sum := by decide
  have hdescent : baseEnd_4404103 < baseStart_4404103 := by decide
  rcases family_descends (prefixWord ++ tailWord_4404103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4404139 : List Nat := [1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 7]
def baseStart_4404139 : Nat := 118140960795 + 4404139 * 2 ^ 59
def prefixEnd_4404139 : Nat := 4983230072969 + 3 ^ 40 * 4404139 * 2
def baseEnd_4404139 : Nat := 2261440176211849519608239

theorem tailTrace_4404139 : CollatzResearch.WordTrace tailWord_4404139 prefixEnd_4404139 2261440176211849519608239 := by
  unfold tailWord_4404139
  simp only [CollatzResearch.WordTrace]
  refine ⟨160632145791564044903231471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107088097194376029935487647 160632145791564044903231471)
  ·
    refine ⟨240948218687346067354847207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160632145791564044903231471 240948218687346067354847207)
    ·
      refine ⟨361422328031019101032270811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240948218687346067354847207 361422328031019101032270811)
      ·
        refine ⟨542133492046528651548406217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 361422328031019101032270811 542133492046528651548406217)
        ·
          refine ⟨406600119034896488661304663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 542133492046528651548406217 406600119034896488661304663)
          ·
            refine ⟨609900178552344732991956995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 406600119034896488661304663 609900178552344732991956995)
            ·
              refine ⟨914850267828517099487935493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 609900178552344732991956995 914850267828517099487935493)
              ·
                refine ⟨171534425217846956153987905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 914850267828517099487935493 171534425217846956153987905)
                ·
                  refine ⟨128650818913385217115490929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 171534425217846956153987905 128650818913385217115490929)
                  ·
                    refine ⟨96488114185038912836618197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 128650818913385217115490929 96488114185038912836618197)
                    ·
                      refine ⟨2261440176211849519608239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 96488114185038912836618197 2261440176211849519608239)
                      ·
                        rfl

theorem cell23_4404139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 7].length) (baseStart_4404139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4404139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4404139 prefixEnd_4404139 := by exact prefixLift 4404139
  have htrace : WordTrace (prefixWord ++ tailWord_4404139) baseStart_4404139 baseEnd_4404139 := by
    simpa [prefixWord, tailWord_4404139, baseEnd_4404139] using wordTrace_append hprefix tailTrace_4404139
  have hstable : (prefixWord ++ tailWord_4404139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4404139).length < 2 ^ (prefixWord ++ tailWord_4404139).sum := by decide
  have hdescent : baseEnd_4404139 < baseStart_4404139 := by decide
  rcases family_descends (prefixWord ++ tailWord_4404139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4404194 : List Nat := [3, 3, 3, 1, 1, 3, 1, 2, 1, 2, 3]
def baseStart_4404194 : Nat := 118140960795 + 4404194 * 2 ^ 59
def prefixEnd_4404194 : Nat := 4983230072969 + 3 ^ 40 * 4404194 * 2
def baseEnd_4404194 : Nat := 2261468417647846804420487

theorem tailTrace_4404194 : CollatzResearch.WordTrace tailWord_4404194 prefixEnd_4404194 2261468417647846804420487 := by
  unfold tailWord_4404194
  simp only [CollatzResearch.WordTrace]
  refine ⟨40158537951591197324120909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107089434537576526197655757 40158537951591197324120909)
  ·
    refine ⟨15059451731846698996545341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40158537951591197324120909 15059451731846698996545341)
    ·
      refine ⟨5647294399442512123704503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15059451731846698996545341 5647294399442512123704503)
      ·
        refine ⟨8470941599163768185556755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5647294399442512123704503 8470941599163768185556755)
        ·
          refine ⟨12706412398745652278335133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8470941599163768185556755 12706412398745652278335133)
          ·
            refine ⟨4764904649529619604375675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12706412398745652278335133 4764904649529619604375675)
            ·
              refine ⟨7147356974294429406563513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4764904649529619604375675 7147356974294429406563513)
              ·
                refine ⟨5360517730720822054922635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7147356974294429406563513 5360517730720822054922635)
                ·
                  refine ⟨8040776596081233082383953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5360517730720822054922635 8040776596081233082383953)
                  ·
                    refine ⟨6030582447060924811787965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8040776596081233082383953 6030582447060924811787965)
                    ·
                      refine ⟨2261468417647846804420487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6030582447060924811787965 2261468417647846804420487)
                      ·
                        rfl

theorem cell23_4404194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_4404194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4404194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4404194 prefixEnd_4404194 := by exact prefixLift 4404194
  have htrace : WordTrace (prefixWord ++ tailWord_4404194) baseStart_4404194 baseEnd_4404194 := by
    simpa [prefixWord, tailWord_4404194, baseEnd_4404194] using wordTrace_append hprefix tailTrace_4404194
  have hstable : (prefixWord ++ tailWord_4404194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4404194).length < 2 ^ (prefixWord ++ tailWord_4404194).sum := by decide
  have hdescent : baseEnd_4404194 < baseStart_4404194 := by decide
  rcases family_descends (prefixWord ++ tailWord_4404194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4404196 : List Nat := [2, 3, 1, 1, 1, 1, 2, 1, 4, 3, 4]
def baseStart_4404196 : Nat := 118140960795 + 4404196 * 2 ^ 59
def prefixEnd_4404196 : Nat := 4983230072969 + 3 ^ 40 * 4404196 * 2
def baseEnd_4404196 : Nat := 2261469444609155796595477

theorem tailTrace_4404196 : CollatzResearch.WordTrace tailWord_4404196 prefixEnd_4404196 2261469444609155796595477 := by
  unfold tailWord_4404196
  simp only [CollatzResearch.WordTrace]
  refine ⟨80317112376178771819028221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107089483168238362425370961 80317112376178771819028221)
  ·
    refine ⟨30118917141067039432135583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80317112376178771819028221 30118917141067039432135583)
    ·
      refine ⟨45178375711600559148203375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30118917141067039432135583 45178375711600559148203375)
      ·
        refine ⟨67767563567400838722305063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45178375711600559148203375 67767563567400838722305063)
        ·
          refine ⟨101651345351101258083457595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67767563567400838722305063 101651345351101258083457595)
          ·
            refine ⟨152477018026651887125186393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101651345351101258083457595 152477018026651887125186393)
            ·
              refine ⟨114357763519988915343889795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152477018026651887125186393 114357763519988915343889795)
              ·
                refine ⟨171536645279983373015834693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114357763519988915343889795 171536645279983373015834693)
                ·
                  refine ⟨32163120989996882440469005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 171536645279983373015834693 32163120989996882440469005)
                  ·
                    refine ⟨12061170371248830915175877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32163120989996882440469005 12061170371248830915175877)
                    ·
                      refine ⟨2261469444609155796595477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12061170371248830915175877 2261469444609155796595477)
                      ·
                        rfl

theorem cell23_4404196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 4, 3, 4].length) (baseStart_4404196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4404196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4404196 prefixEnd_4404196 := by exact prefixLift 4404196
  have htrace : WordTrace (prefixWord ++ tailWord_4404196) baseStart_4404196 baseEnd_4404196 := by
    simpa [prefixWord, tailWord_4404196, baseEnd_4404196] using wordTrace_append hprefix tailTrace_4404196
  have hstable : (prefixWord ++ tailWord_4404196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4404196).length < 2 ^ (prefixWord ++ tailWord_4404196).sum := by decide
  have hdescent : baseEnd_4404196 < baseStart_4404196 := by decide
  rcases family_descends (prefixWord ++ tailWord_4404196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4404217 : List Nat := [1, 2, 1, 3, 1, 3, 5, 1, 1, 3, 2]
def baseStart_4404217 : Nat := 118140960795 + 4404217 * 2 ^ 59
def prefixEnd_4404217 : Nat := 4983230072969 + 3 ^ 40 * 4404217 * 2
def baseEnd_4404217 : Nat := 2261480227702900214432881

theorem tailTrace_4404217 : CollatzResearch.WordTrace tailWord_4404217 prefixEnd_4404217 2261480227702900214432881 := by
  unfold tailWord_4404217
  simp only [CollatzResearch.WordTrace]
  refine ⟨160634990685281464224570905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107089993790187642816380603 160634990685281464224570905)
  ·
    refine ⟨120476243013961098168428179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160634990685281464224570905 120476243013961098168428179)
    ·
      refine ⟨180714364520941647252642269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120476243013961098168428179 180714364520941647252642269)
      ·
        refine ⟨67767886695353117719740851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 180714364520941647252642269 67767886695353117719740851)
        ·
          refine ⟨101651830043029676579611277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67767886695353117719740851 101651830043029676579611277)
          ·
            refine ⟨38119436266136128717354229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101651830043029676579611277 38119436266136128717354229)
            ·
              refine ⟨3573697149950262067251959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38119436266136128717354229 3573697149950262067251959)
              ·
                refine ⟨5360545724925393100877939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3573697149950262067251959 5360545724925393100877939)
                ·
                  refine ⟨8040818587388089651316909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5360545724925393100877939 8040818587388089651316909)
                  ·
                    refine ⟨3015306970270533619243841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8040818587388089651316909 3015306970270533619243841)
                    ·
                      refine ⟨2261480227702900214432881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3015306970270533619243841 2261480227702900214432881)
                      ·
                        rfl

theorem cell23_4404217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 5, 1, 1, 3, 2].length) (baseStart_4404217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4404217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4404217 prefixEnd_4404217 := by exact prefixLift 4404217
  have htrace : WordTrace (prefixWord ++ tailWord_4404217) baseStart_4404217 baseEnd_4404217 := by
    simpa [prefixWord, tailWord_4404217, baseEnd_4404217] using wordTrace_append hprefix tailTrace_4404217
  have hstable : (prefixWord ++ tailWord_4404217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4404217).length < 2 ^ (prefixWord ++ tailWord_4404217).sum := by decide
  have hdescent : baseEnd_4404217 < baseStart_4404217 := by decide
  rcases family_descends (prefixWord ++ tailWord_4404217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4404247 : List Nat := [1, 1, 3, 5, 1, 2, 2, 1, 1, 4, 2]
def baseStart_4404247 : Nat := 118140960795 + 4404247 * 2 ^ 59
def prefixEnd_4404247 : Nat := 4983230072969 + 3 ^ 40 * 4404247 * 2
def baseEnd_4404247 : Nat := 2261495632122535097057743

theorem tailTrace_4404247 : CollatzResearch.WordTrace tailWord_4404247 prefixEnd_4404247 2261495632122535097057743 := by
  unfold tailWord_4404247
  simp only [CollatzResearch.WordTrace]
  refine ⟨160636084875172779348162995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107090723250115186232108663 160636084875172779348162995)
  ·
    refine ⟨240954127312759169022244493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160636084875172779348162995 240954127312759169022244493)
    ·
      refine ⟨90357797742284688383341685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 240954127312759169022244493 90357797742284688383341685)
      ·
        refine ⟨8471043538339189535938283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 90357797742284688383341685 8471043538339189535938283)
        ·
          refine ⟨12706565307508784303907425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8471043538339189535938283 12706565307508784303907425)
          ·
            refine ⟨9529923980631588227930569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12706565307508784303907425 9529923980631588227930569)
            ·
              refine ⟨7147442985473691170947927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9529923980631588227930569 7147442985473691170947927)
              ·
                refine ⟨10721164478210536756421891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7147442985473691170947927 10721164478210536756421891)
                ·
                  refine ⟨16081746717315805134632837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10721164478210536756421891 16081746717315805134632837)
                  ·
                    refine ⟨3015327509496713462743657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16081746717315805134632837 3015327509496713462743657)
                    ·
                      refine ⟨2261495632122535097057743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3015327509496713462743657 2261495632122535097057743)
                      ·
                        rfl

theorem cell23_4404247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_4404247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4404247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4404247 prefixEnd_4404247 := by exact prefixLift 4404247
  have htrace : WordTrace (prefixWord ++ tailWord_4404247) baseStart_4404247 baseEnd_4404247 := by
    simpa [prefixWord, tailWord_4404247, baseEnd_4404247] using wordTrace_append hprefix tailTrace_4404247
  have hstable : (prefixWord ++ tailWord_4404247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4404247).length < 2 ^ (prefixWord ++ tailWord_4404247).sum := by decide
  have hdescent : baseEnd_4404247 < baseStart_4404247 := by decide
  rcases family_descends (prefixWord ++ tailWord_4404247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4404313 : List Nat := [1, 2, 1, 2, 2, 1, 2, 3, 5, 4]
def baseStart_4404313 : Nat := 118140960795 + 4404313 * 2 ^ 59
def prefixEnd_4404313 : Nat := 4983230072969 + 3 ^ 40 * 4404313 * 2
def baseEnd_4404313 : Nat := 753843173948577279610813

theorem tailTrace_4404313 : CollatzResearch.WordTrace tailWord_4404313 prefixEnd_4404313 753843173948577279610813 := by
  unfold tailWord_4404313
  simp only [CollatzResearch.WordTrace]
  refine ⟨160638492092933672620065593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107092328061955781746710395 160638492092933672620065593)
  ·
    refine ⟨120478869069700254465049195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160638492092933672620065593 120478869069700254465049195)
    ·
      refine ⟨180718303604550381697573793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120478869069700254465049195 180718303604550381697573793)
      ·
        refine ⟨135538727703412786273180345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180718303604550381697573793 135538727703412786273180345)
        ·
          refine ⟨101654045777559589704885259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135538727703412786273180345 101654045777559589704885259)
          ·
            refine ⟨152481068666339384557327889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101654045777559589704885259 152481068666339384557327889)
            ·
              refine ⟨114360801499754538417995917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152481068666339384557327889 114360801499754538417995917)
              ·
                refine ⟨42885300562407951906748469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 114360801499754538417995917 42885300562407951906748469)
                ·
                  refine ⟨4020496927725745491257669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42885300562407951906748469 4020496927725745491257669)
                  ·
                    refine ⟨753843173948577279610813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4020496927725745491257669 753843173948577279610813)
                    ·
                      rfl

theorem cell23_4404313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 5, 4].length) (baseStart_4404313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4404313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4404313 prefixEnd_4404313 := by exact prefixLift 4404313
  have htrace : WordTrace (prefixWord ++ tailWord_4404313) baseStart_4404313 baseEnd_4404313 := by
    simpa [prefixWord, tailWord_4404313, baseEnd_4404313] using wordTrace_append hprefix tailTrace_4404313
  have hstable : (prefixWord ++ tailWord_4404313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4404313).length < 2 ^ (prefixWord ++ tailWord_4404313).sum := by decide
  have hdescent : baseEnd_4404313 < baseStart_4404313 := by decide
  rcases family_descends (prefixWord ++ tailWord_4404313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4404343 : List Nat := [1, 1, 3, 1, 1, 4, 2, 4, 6]
def baseStart_4404343 : Nat := 118140960795 + 4404343 * 2 ^ 59
def prefixEnd_4404343 : Nat := 4983230072969 + 3 ^ 40 * 4404343 * 2
def baseEnd_4404343 : Nat := 251282769585040746828589

theorem tailTrace_4404343 : CollatzResearch.WordTrace tailWord_4404343 prefixEnd_4404343 251282769585040746828589 := by
  unfold tailWord_4404343
  simp only [CollatzResearch.WordTrace]
  refine ⟨160639586282824987743657683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107093057521883325162438455 160639586282824987743657683)
  ·
    refine ⟨240959379424237481615486525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160639586282824987743657683 240959379424237481615486525)
    ·
      refine ⟨90359767284089055605807447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 240959379424237481615486525 90359767284089055605807447)
      ·
        refine ⟨135539650926133583408711171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90359767284089055605807447 135539650926133583408711171)
        ·
          refine ⟨203309476389200375113066757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135539650926133583408711171 203309476389200375113066757)
          ·
            refine ⟨38120526822975070333700017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 203309476389200375113066757 38120526822975070333700017)
            ·
              refine ⟨28590395117231302750275013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38120526822975070333700017 28590395117231302750275013)
              ·
                refine ⟨5360699084480869265676565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28590395117231302750275013 5360699084480869265676565)
                ·
                  refine ⟨251282769585040746828589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5360699084480869265676565 251282769585040746828589)
                  ·
                    rfl

theorem cell23_4404343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 4, 6].length) (baseStart_4404343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4404343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4404343 prefixEnd_4404343 := by exact prefixLift 4404343
  have htrace : WordTrace (prefixWord ++ tailWord_4404343) baseStart_4404343 baseEnd_4404343 := by
    simpa [prefixWord, tailWord_4404343, baseEnd_4404343] using wordTrace_append hprefix tailTrace_4404343
  have hstable : (prefixWord ++ tailWord_4404343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4404343).length < 2 ^ (prefixWord ++ tailWord_4404343).sum := by decide
  have hdescent : baseEnd_4404343 < baseStart_4404343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4404343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4404410 : List Nat := [3, 1, 1, 1, 2, 2, 1, 2, 2, 6, 2]
def baseStart_4404410 : Nat := 118140960795 + 4404410 * 2 ^ 59
def prefixEnd_4404410 : Nat := 4983230072969 + 3 ^ 40 * 4404410 * 2
def baseEnd_4404410 : Nat := 2261579329469217959319493

theorem tailTrace_4404410 : CollatzResearch.WordTrace tailWord_4404410 prefixEnd_4404410 2261579329469217959319493 := by
  unfold tailWord_4404410
  simp only [CollatzResearch.WordTrace]
  refine ⟨40160507493395564546586671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107094686649054838790897789 40160507493395564546586671)
  ·
    refine ⟨60240761240093346819880007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40160507493395564546586671 60240761240093346819880007)
    ·
      refine ⟨90361141860140020229820011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60240761240093346819880007 90361141860140020229820011)
      ·
        refine ⟨135541712790210030344730017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90361141860140020229820011 135541712790210030344730017)
        ·
          refine ⟨101656284592657522758547513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135541712790210030344730017 101656284592657522758547513)
          ·
            refine ⟨76242213444493142068910635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101656284592657522758547513 76242213444493142068910635)
            ·
              refine ⟨114363320166739713103365953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76242213444493142068910635 114363320166739713103365953)
              ·
                refine ⟨85772490125054784827524465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114363320166739713103365953 85772490125054784827524465)
                ·
                  refine ⟨64329367593791088620643349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85772490125054784827524465 64329367593791088620643349)
                  ·
                    refine ⟨3015439105958957279092657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 64329367593791088620643349 3015439105958957279092657)
                    ·
                      refine ⟨2261579329469217959319493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3015439105958957279092657 2261579329469217959319493)
                      ·
                        rfl

theorem cell23_4404410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 2, 6, 2].length) (baseStart_4404410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4404410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4404410 prefixEnd_4404410 := by exact prefixLift 4404410
  have htrace : WordTrace (prefixWord ++ tailWord_4404410) baseStart_4404410 baseEnd_4404410 := by
    simpa [prefixWord, tailWord_4404410, baseEnd_4404410] using wordTrace_append hprefix tailTrace_4404410
  have hstable : (prefixWord ++ tailWord_4404410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4404410).length < 2 ^ (prefixWord ++ tailWord_4404410).sum := by decide
  have hdescent : baseEnd_4404410 < baseStart_4404410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4404410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4404423 : List Nat := [1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 6]
def baseStart_4404423 : Nat := 118140960795 + 4404423 * 2 ^ 59
def prefixEnd_4404423 : Nat := 4983230072969 + 3 ^ 40 * 4404423 * 2
def baseEnd_4404423 : Nat := 2261586004717726408456933

theorem tailTrace_4404423 : CollatzResearch.WordTrace tailWord_4404423 prefixEnd_4404423 2261586004717726408456933 := by
  unfold tailWord_4404423
  simp only [CollatzResearch.WordTrace]
  refine ⟨160642504122535161406569923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107095002748356774271046615 160642504122535161406569923)
  ·
    refine ⟨240963756183802742109854885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160642504122535161406569923 240963756183802742109854885)
    ·
      refine ⟨45180704284463014145597791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 240963756183802742109854885 45180704284463014145597791)
      ·
        refine ⟨67771056426694521218396687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45180704284463014145597791 67771056426694521218396687)
        ·
          refine ⟨101656584640041781827595031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67771056426694521218396687 101656584640041781827595031)
          ·
            refine ⟨152484876960062672741392547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101656584640041781827595031 152484876960062672741392547)
            ·
              refine ⟨228727315440094009112088821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152484876960062672741392547 228727315440094009112088821)
              ·
                refine ⟨21443185822508813354258327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 228727315440094009112088821 21443185822508813354258327)
                ·
                  refine ⟨32164778733763220031387491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21443185822508813354258327 32164778733763220031387491)
                  ·
                    refine ⟨48247168100644830047081237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32164778733763220031387491 48247168100644830047081237)
                    ·
                      refine ⟨2261586004717726408456933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48247168100644830047081237 2261586004717726408456933)
                      ·
                        rfl

theorem cell23_4404423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 6].length) (baseStart_4404423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4404423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4404423 prefixEnd_4404423 := by exact prefixLift 4404423
  have htrace : WordTrace (prefixWord ++ tailWord_4404423) baseStart_4404423 baseEnd_4404423 := by
    simpa [prefixWord, tailWord_4404423, baseEnd_4404423] using wordTrace_append hprefix tailTrace_4404423
  have hstable : (prefixWord ++ tailWord_4404423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4404423).length < 2 ^ (prefixWord ++ tailWord_4404423).sum := by decide
  have hdescent : baseEnd_4404423 < baseStart_4404423 := by decide
  rcases family_descends (prefixWord ++ tailWord_4404423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4404461 : List Nat := [1, 5, 1, 2, 2, 2, 2, 1, 3, 2, 2]
def baseStart_4404461 : Nat := 118140960795 + 4404461 * 2 ^ 59
def prefixEnd_4404461 : Nat := 4983230072969 + 3 ^ 40 * 4404461 * 2
def baseEnd_4404461 : Nat := 2261605516982597259781759

theorem tailTrace_4404461 : CollatzResearch.WordTrace tailWord_4404461 prefixEnd_4404461 2261605516982597259781759 := by
  unfold tailWord_4404461
  simp only [CollatzResearch.WordTrace]
  refine ⟨160643890096397493896453237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107095926730931662597635491 160643890096397493896453237)
  ·
    refine ⟨15060364696537265052792491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 160643890096397493896453237 15060364696537265052792491)
    ·
      refine ⟨22590547044805897579188737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15060364696537265052792491 22590547044805897579188737)
      ·
        refine ⟨16942910283604423184391553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22590547044805897579188737 16942910283604423184391553)
        ·
          refine ⟨12707182712703317388293665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16942910283604423184391553 12707182712703317388293665)
          ·
            refine ⟨9530387034527488041220249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12707182712703317388293665 9530387034527488041220249)
            ·
              refine ⟨7147790275895616030915187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9530387034527488041220249 7147790275895616030915187)
              ·
                refine ⟨10721685413843424046372781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7147790275895616030915187 10721685413843424046372781)
                ·
                  refine ⟨4020632030191284017389793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10721685413843424046372781 4020632030191284017389793)
                  ·
                    refine ⟨3015474022643463013042345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4020632030191284017389793 3015474022643463013042345)
                    ·
                      refine ⟨2261605516982597259781759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3015474022643463013042345 2261605516982597259781759)
                      ·
                        rfl

theorem cell23_4404461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 1, 3, 2, 2].length) (baseStart_4404461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4404461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4404461 prefixEnd_4404461 := by exact prefixLift 4404461
  have htrace : WordTrace (prefixWord ++ tailWord_4404461) baseStart_4404461 baseEnd_4404461 := by
    simpa [prefixWord, tailWord_4404461, baseEnd_4404461] using wordTrace_append hprefix tailTrace_4404461
  have hstable : (prefixWord ++ tailWord_4404461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4404461).length < 2 ^ (prefixWord ++ tailWord_4404461).sum := by decide
  have hdescent : baseEnd_4404461 < baseStart_4404461 := by decide
  rcases family_descends (prefixWord ++ tailWord_4404461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4404504 : List Nat := [2, 1, 2, 3, 1, 3, 2, 3, 1, 3, 2]
def baseStart_4404504 : Nat := 118140960795 + 4404504 * 2 ^ 59
def prefixEnd_4404504 : Nat := 4983230072969 + 3 ^ 40 * 4404504 * 2
def baseEnd_4404504 : Nat := 2261627596650740591544061

theorem tailTrace_4404504 : CollatzResearch.WordTrace tailWord_4404504 prefixEnd_4404504 2261627596650740591544061 := by
  unfold tailWord_4404504
  simp only [CollatzResearch.WordTrace]
  refine ⟨80322729217620856120134283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107096972290161141493512377 80322729217620856120134283)
  ·
    refine ⟨120484093826431284180201425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80322729217620856120134283 120484093826431284180201425)
    ·
      refine ⟨90363070369823463135151069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120484093826431284180201425 90363070369823463135151069)
      ·
        refine ⟨33886151388683798675681651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90363070369823463135151069 33886151388683798675681651)
        ·
          refine ⟨50829227083025698013522477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33886151388683798675681651 50829227083025698013522477)
          ·
            refine ⟨19060960156134636755070929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50829227083025698013522477 19060960156134636755070929)
            ·
              refine ⟨14295720117100977566303197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19060960156134636755070929 14295720117100977566303197)
              ·
                refine ⟨5360895043912866587363699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14295720117100977566303197 5360895043912866587363699)
                ·
                  refine ⟨8041342565869299881045549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5360895043912866587363699 8041342565869299881045549)
                  ·
                    refine ⟨3015503462200987455392081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8041342565869299881045549 3015503462200987455392081)
                    ·
                      refine ⟨2261627596650740591544061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3015503462200987455392081 2261627596650740591544061)
                      ·
                        rfl

theorem cell23_4404504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 3, 1, 3, 2].length) (baseStart_4404504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4404504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4404504 prefixEnd_4404504 := by exact prefixLift 4404504
  have htrace : WordTrace (prefixWord ++ tailWord_4404504) baseStart_4404504 baseEnd_4404504 := by
    simpa [prefixWord, tailWord_4404504, baseEnd_4404504] using wordTrace_append hprefix tailTrace_4404504
  have hstable : (prefixWord ++ tailWord_4404504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4404504).length < 2 ^ (prefixWord ++ tailWord_4404504).sum := by decide
  have hdescent : baseEnd_4404504 < baseStart_4404504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4404504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4404523 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 13]
def baseStart_4404523 : Nat := 118140960795 + 4404523 * 2 ^ 59
def prefixEnd_4404523 : Nat := 4983230072969 + 3 ^ 40 * 4404523 * 2
def baseEnd_4404523 : Nat := 251293039198130668578497

theorem tailTrace_4404523 : CollatzResearch.WordTrace tailWord_4404523 prefixEnd_4404523 251293039198130668578497 := by
  unfold tailWord_4404523
  simp only [CollatzResearch.WordTrace]
  refine ⟨160646151422172878485210223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107097434281448585656806815 160646151422172878485210223)
  ·
    refine ⟨240969227133259317727815335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160646151422172878485210223 240969227133259317727815335)
    ·
      refine ⟨361453840699888976591723003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240969227133259317727815335 361453840699888976591723003)
      ·
        refine ⟨542180761049833464887584505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 361453840699888976591723003 542180761049833464887584505)
        ·
          refine ⟨406635570787375098665688379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 542180761049833464887584505 406635570787375098665688379)
          ·
            refine ⟨609953356181062647998532569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 406635570787375098665688379 609953356181062647998532569)
            ·
              refine ⟨457465017135796985998899427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 609953356181062647998532569 457465017135796985998899427)
              ·
                refine ⟨686197525703695478998349141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 457465017135796985998899427 686197525703695478998349141)
                ·
                  refine ⟨251293039198130668578497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 13 686197525703695478998349141 251293039198130668578497)
                  ·
                    rfl

theorem cell23_4404523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 13].length) (baseStart_4404523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4404523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4404523 prefixEnd_4404523 := by exact prefixLift 4404523
  have htrace : WordTrace (prefixWord ++ tailWord_4404523) baseStart_4404523 baseEnd_4404523 := by
    simpa [prefixWord, tailWord_4404523, baseEnd_4404523] using wordTrace_append hprefix tailTrace_4404523
  have hstable : (prefixWord ++ tailWord_4404523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4404523).length < 2 ^ (prefixWord ++ tailWord_4404523).sum := by decide
  have hdescent : baseEnd_4404523 < baseStart_4404523 := by decide
  rcases family_descends (prefixWord ++ tailWord_4404523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4404584 : List Nat := [2, 1, 4, 2, 3, 1, 1, 1, 2, 3, 3]
def baseStart_4404584 : Nat := 118140960795 + 4404584 * 2 ^ 59
def prefixEnd_4404584 : Nat := 4983230072969 + 3 ^ 40 * 4404584 * 2
def baseEnd_4404584 : Nat := 2261668675103100278543693

theorem tailTrace_4404584 : CollatzResearch.WordTrace tailWord_4404584 prefixEnd_4404584 2261668675103100278543693 := by
  unfold tailWord_4404584
  simp only [CollatzResearch.WordTrace]
  refine ⟨80324188137475942951590403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107098917516634590602120537 80324188137475942951590403)
  ·
    refine ⟨120486282206213914427385605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80324188137475942951590403 120486282206213914427385605)
    ·
      refine ⟨22591177913665108955134801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120486282206213914427385605 22591177913665108955134801)
      ·
        refine ⟨16943383435248831716351101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22591177913665108955134801 16943383435248831716351101)
        ·
          refine ⟨6353768788218311893631663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16943383435248831716351101 6353768788218311893631663)
          ·
            refine ⟨9530653182327467840447495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6353768788218311893631663 9530653182327467840447495)
            ·
              refine ⟨14295979773491201760671243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9530653182327467840447495 14295979773491201760671243)
              ·
                refine ⟨21443969660236802641006865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14295979773491201760671243 21443969660236802641006865)
                ·
                  refine ⟨16082977245177601980755149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21443969660236802641006865 16082977245177601980755149)
                  ·
                    refine ⟨6031116466941600742783181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16082977245177601980755149 6031116466941600742783181)
                    ·
                      refine ⟨2261668675103100278543693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6031116466941600742783181 2261668675103100278543693)
                      ·
                        rfl

theorem cell23_4404584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_4404584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4404584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4404584 prefixEnd_4404584 := by exact prefixLift 4404584
  have htrace : WordTrace (prefixWord ++ tailWord_4404584) baseStart_4404584 baseEnd_4404584 := by
    simpa [prefixWord, tailWord_4404584, baseEnd_4404584] using wordTrace_append hprefix tailTrace_4404584
  have hstable : (prefixWord ++ tailWord_4404584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4404584).length < 2 ^ (prefixWord ++ tailWord_4404584).sum := by decide
  have hdescent : baseEnd_4404584 < baseStart_4404584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4404584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4404607 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 6, 4, 2]
def baseStart_4404607 : Nat := 118140960795 + 4404607 * 2 ^ 59
def prefixEnd_4404607 : Nat := 4983230072969 + 3 ^ 40 * 4404607 * 2
def baseEnd_4404607 : Nat := 2261680485158153688556087

theorem tailTrace_4404607 : CollatzResearch.WordTrace tailWord_4404607 prefixEnd_4404607 2261680485158153688556087 := by
  unfold tailWord_4404607
  simp only [CollatzResearch.WordTrace]
  refine ⟨160649215153868560831268075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107099476769245707220845383 160649215153868560831268075)
  ·
    refine ⟨240973822730802841246902113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160649215153868560831268075 240973822730802841246902113)
    ·
      refine ⟨180730367048102130935176585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 240973822730802841246902113 180730367048102130935176585)
      ·
        refine ⟨135547775286076598201382439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180730367048102130935176585 135547775286076598201382439)
        ·
          refine ⟨203321662929114897302073659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135547775286076598201382439 203321662929114897302073659)
          ·
            refine ⟨304982494393672345953110489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203321662929114897302073659 304982494393672345953110489)
            ·
              refine ⟨228736870795254259464832867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 304982494393672345953110489 228736870795254259464832867)
              ·
                refine ⟨343105306192881389197249301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 228736870795254259464832867 343105306192881389197249301)
                ·
                  refine ⟨16083061227791315118621061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 343105306192881389197249301 16083061227791315118621061)
                  ·
                    refine ⟨3015573980210871584741449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16083061227791315118621061 3015573980210871584741449)
                    ·
                      refine ⟨2261680485158153688556087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3015573980210871584741449 2261680485158153688556087)
                      ·
                        rfl

theorem cell23_4404607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 6, 4, 2].length) (baseStart_4404607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4404607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4404607 prefixEnd_4404607 := by exact prefixLift 4404607
  have htrace : WordTrace (prefixWord ++ tailWord_4404607) baseStart_4404607 baseEnd_4404607 := by
    simpa [prefixWord, tailWord_4404607, baseEnd_4404607] using wordTrace_append hprefix tailTrace_4404607
  have hstable : (prefixWord ++ tailWord_4404607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4404607).length < 2 ^ (prefixWord ++ tailWord_4404607).sum := by decide
  have hdescent : baseEnd_4404607 < baseStart_4404607 := by decide
  rcases family_descends (prefixWord ++ tailWord_4404607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4404620 : List Nat := [2, 2, 1, 2, 1, 3, 1, 1, 1, 3, 6]
def baseStart_4404620 : Nat := 118140960795 + 4404620 * 2 ^ 59
def prefixEnd_4404620 : Nat := 4983230072969 + 3 ^ 40 * 4404620 * 2
def baseEnd_4404620 : Nat := 2261687160406662137693527

theorem tailTrace_4404620 : CollatzResearch.WordTrace tailWord_4404620 prefixEnd_4404620 2261687160406662137693527 := by
  unfold tailWord_4404620
  simp only [CollatzResearch.WordTrace]
  refine ⟨80324844651410732025745657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107099792868547642700994209 80324844651410732025745657)
  ·
    refine ⟨60243633488558049019309243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80324844651410732025745657 60243633488558049019309243)
    ·
      refine ⟨90365450232837073528963865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60243633488558049019309243 90365450232837073528963865)
      ·
        refine ⟨67774087674627805146722899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90365450232837073528963865 67774087674627805146722899)
        ·
          refine ⟨101661131511941707720084349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67774087674627805146722899 101661131511941707720084349)
          ·
            refine ⟨38122924316978140395031631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101661131511941707720084349 38122924316978140395031631)
            ·
              refine ⟨57184386475467210592547447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38122924316978140395031631 57184386475467210592547447)
              ·
                refine ⟨85776579713200815888821171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57184386475467210592547447 85776579713200815888821171)
                ·
                  refine ⟨128664869569801223833231757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85776579713200815888821171 128664869569801223833231757)
                  ·
                    refine ⟨48249326088675458937461909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 128664869569801223833231757 48249326088675458937461909)
                    ·
                      refine ⟨2261687160406662137693527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48249326088675458937461909 2261687160406662137693527)
                      ·
                        rfl

theorem cell23_4404620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_4404620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4404620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4404620 prefixEnd_4404620 := by exact prefixLift 4404620
  have htrace : WordTrace (prefixWord ++ tailWord_4404620) baseStart_4404620 baseEnd_4404620 := by
    simpa [prefixWord, tailWord_4404620, baseEnd_4404620] using wordTrace_append hprefix tailTrace_4404620
  have hstable : (prefixWord ++ tailWord_4404620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4404620).length < 2 ^ (prefixWord ++ tailWord_4404620).sum := by decide
  have hdescent : baseEnd_4404620 < baseStart_4404620 := by decide
  rcases family_descends (prefixWord ++ tailWord_4404620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4404634 : List Nat := [3, 1, 1, 4, 1, 1, 4, 1, 3, 4]
def baseStart_4404634 : Nat := 118140960795 + 4404634 * 2 ^ 59
def prefixEnd_4404634 : Nat := 4983230072969 + 3 ^ 40 * 4404634 * 2
def baseEnd_4404634 : Nat := 753898116378608360972821

theorem tailTrace_4404634 : CollatzResearch.WordTrace tailWord_4404634 prefixEnd_4404634 753898116378608360972821 := by
  unfold tailWord_4404634
  simp only [CollatzResearch.WordTrace]
  refine ⟨40162549981192686110625239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107100133283180496295000637 40162549981192686110625239)
  ·
    refine ⟨60243824971789029165937859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40162549981192686110625239 60243824971789029165937859)
    ·
      refine ⟨90365737457683543748906789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60243824971789029165937859 90365737457683543748906789)
      ·
        refine ⟨16943575773315664452920023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90365737457683543748906789 16943575773315664452920023)
        ·
          refine ⟨25415363659973496679380035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16943575773315664452920023 25415363659973496679380035)
          ·
            refine ⟨38123045489960245019070053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25415363659973496679380035 38123045489960245019070053)
            ·
              refine ⟨7148071029367545941075635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38123045489960245019070053 7148071029367545941075635)
              ·
                refine ⟨10722106544051318911613453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7148071029367545941075635 10722106544051318911613453)
                ·
                  refine ⟨4020789954019244591855045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10722106544051318911613453 4020789954019244591855045)
                  ·
                    refine ⟨753898116378608360972821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4020789954019244591855045 753898116378608360972821)
                    ·
                      rfl

theorem cell23_4404634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 1, 3, 4].length) (baseStart_4404634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4404634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4404634 prefixEnd_4404634 := by exact prefixLift 4404634
  have htrace : WordTrace (prefixWord ++ tailWord_4404634) baseStart_4404634 baseEnd_4404634 := by
    simpa [prefixWord, tailWord_4404634, baseEnd_4404634] using wordTrace_append hprefix tailTrace_4404634
  have hstable : (prefixWord ++ tailWord_4404634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4404634).length < 2 ^ (prefixWord ++ tailWord_4404634).sum := by decide
  have hdescent : baseEnd_4404634 < baseStart_4404634 := by decide
  rcases family_descends (prefixWord ++ tailWord_4404634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4404657 : List Nat := [1, 2, 2, 4, 1, 1, 1, 1, 2, 5, 3]
def baseStart_4404657 : Nat := 118140960795 + 4404657 * 2 ^ 59
def prefixEnd_4404657 : Nat := 4983230072969 + 3 ^ 40 * 4404657 * 2
def baseEnd_4404657 : Nat := 2261706159190878492930857

theorem tailTrace_4404657 : CollatzResearch.WordTrace tailWord_4404657 prefixEnd_4404657 2261706159190878492930857 := by
  unfold tailWord_4404657
  simp only [CollatzResearch.WordTrace]
  refine ⟨160651038803687419370588225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107100692535791612913725483 160651038803687419370588225)
  ·
    refine ⟨120488279102765564527941169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160651038803687419370588225 120488279102765564527941169)
    ·
      refine ⟨90366209327074173395955877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120488279102765564527941169 90366209327074173395955877)
      ·
        refine ⟨16943664248826407511741727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90366209327074173395955877 16943664248826407511741727)
        ·
          refine ⟨25415496373239611267612591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16943664248826407511741727 25415496373239611267612591)
          ·
            refine ⟨38123244559859416901418887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25415496373239611267612591 38123244559859416901418887)
            ·
              refine ⟨57184866839789125352128331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38123244559859416901418887 57184866839789125352128331)
              ·
                refine ⟨85777300259683688028192497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57184866839789125352128331 85777300259683688028192497)
                ·
                  refine ⟨64332975194762766021144373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85777300259683688028192497 64332975194762766021144373)
                  ·
                    refine ⟨6031216424509009314482285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 64332975194762766021144373 6031216424509009314482285)
                    ·
                      refine ⟨2261706159190878492930857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6031216424509009314482285 2261706159190878492930857)
                      ·
                        rfl

theorem cell23_4404657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_4404657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4404657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4404657 prefixEnd_4404657 := by exact prefixLift 4404657
  have htrace : WordTrace (prefixWord ++ tailWord_4404657) baseStart_4404657 baseEnd_4404657 := by
    simpa [prefixWord, tailWord_4404657, baseEnd_4404657] using wordTrace_append hprefix tailTrace_4404657
  have hstable : (prefixWord ++ tailWord_4404657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4404657).length < 2 ^ (prefixWord ++ tailWord_4404657).sum := by decide
  have hdescent : baseEnd_4404657 < baseStart_4404657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4404657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4404711 : List Nat := [1, 1, 5, 2, 1, 4, 1, 2, 1, 5]
def baseStart_4404711 : Nat := 118140960795 + 4404711 * 2 ^ 59
def prefixEnd_4404711 : Nat := 4983230072969 + 3 ^ 40 * 4404711 * 2
def baseEnd_4404711 : Nat := 753911295715407093885203

theorem tailTrace_4404711 : CollatzResearch.WordTrace tailWord_4404711 prefixEnd_4404711 753911295715407093885203 := by
  unfold tailWord_4404711
  simp only [CollatzResearch.WordTrace]
  refine ⟨160653008345491786593053987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107102005563661191062035991 160653008345491786593053987)
  ·
    refine ⟨240979512518237679889580981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160653008345491786593053987 240979512518237679889580981)
    ·
      refine ⟨22591829298584782489648217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 240979512518237679889580981 22591829298584782489648217)
      ·
        refine ⟨16943871973938586867236163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22591829298584782489648217 16943871973938586867236163)
        ·
          refine ⟨25415807960907880300854245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16943871973938586867236163 25415807960907880300854245)
          ·
            refine ⟨4765463992670227556410171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25415807960907880300854245 4765463992670227556410171)
            ·
              refine ⟨7148195989005341334615257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4765463992670227556410171 7148195989005341334615257)
              ·
                refine ⟨5361146991754006000961443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7148195989005341334615257 5361146991754006000961443)
                ·
                  refine ⟨8041720487631009001442165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5361146991754006000961443 8041720487631009001442165)
                  ·
                    refine ⟨753911295715407093885203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8041720487631009001442165 753911295715407093885203)
                    ·
                      rfl

theorem cell23_4404711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 2, 1, 5].length) (baseStart_4404711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4404711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4404711 prefixEnd_4404711 := by exact prefixLift 4404711
  have htrace : WordTrace (prefixWord ++ tailWord_4404711) baseStart_4404711 baseEnd_4404711 := by
    simpa [prefixWord, tailWord_4404711, baseEnd_4404711] using wordTrace_append hprefix tailTrace_4404711
  have hstable : (prefixWord ++ tailWord_4404711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4404711).length < 2 ^ (prefixWord ++ tailWord_4404711).sum := by decide
  have hdescent : baseEnd_4404711 < baseStart_4404711 := by decide
  rcases family_descends (prefixWord ++ tailWord_4404711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4404737 : List Nat := [1, 2, 4, 1, 4, 11]
def baseStart_4404737 : Nat := 118140960795 + 4404737 * 2 ^ 59
def prefixEnd_4404737 : Nat := 4983230072969 + 3 ^ 40 * 4404737 * 2
def baseEnd_4404737 : Nat := 9307601801000980164323

theorem tailTrace_4404737 : CollatzResearch.WordTrace tailWord_4404737 prefixEnd_4404737 9307601801000980164323 := by
  unfold tailWord_4404737
  simp only [CollatzResearch.WordTrace]
  refine ⟨160653956643397593033500465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107102637762265062022333643 160653956643397593033500465)
  ·
    refine ⟨120490467482548194775125349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160653956643397593033500465 120490467482548194775125349)
    ·
      refine ⟨22591962652977786520336003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120490467482548194775125349 22591962652977786520336003)
      ·
        refine ⟨33887943979466679780504005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22591962652977786520336003 33887943979466679780504005)
        ·
          refine ⟨6353989496150002458844501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33887943979466679780504005 6353989496150002458844501)
          ·
            refine ⟨9307601801000980164323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 6353989496150002458844501 9307601801000980164323)
            ·
              rfl

theorem cell23_4404737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 11].length) (baseStart_4404737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4404737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4404737 prefixEnd_4404737 := by exact prefixLift 4404737
  have htrace : WordTrace (prefixWord ++ tailWord_4404737) baseStart_4404737 baseEnd_4404737 := by
    simpa [prefixWord, tailWord_4404737, baseEnd_4404737] using wordTrace_append hprefix tailTrace_4404737
  have hstable : (prefixWord ++ tailWord_4404737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4404737).length < 2 ^ (prefixWord ++ tailWord_4404737).sum := by decide
  have hdescent : baseEnd_4404737 < baseStart_4404737 := by decide
  rcases family_descends (prefixWord ++ tailWord_4404737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4404782 : List Nat := [4, 1, 3, 1, 2, 2, 2, 3, 1, 2, 2]
def baseStart_4404782 : Nat := 118140960795 + 4404782 * 2 ^ 59
def prefixEnd_4404782 : Nat := 4983230072969 + 3 ^ 40 * 4404782 * 2
def baseEnd_4404782 : Nat := 2261770344272690503867783

theorem tailTrace_4404782 : CollatzResearch.WordTrace tailWord_4404782 prefixEnd_4404782 2261770344272690503867783 := by
  unfold tailWord_4404782
  simp only [CollatzResearch.WordTrace]
  refine ⟨20081949741029320714861075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107103731952156377145925733 20081949741029320714861075)
  ·
    refine ⟨30122924611543981072291613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20081949741029320714861075 30122924611543981072291613)
    ·
      refine ⟨11296096729328992902109355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30122924611543981072291613 11296096729328992902109355)
      ·
        refine ⟨16944145093993489353164033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11296096729328992902109355 16944145093993489353164033)
        ·
          refine ⟨12708108820495117014873025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16944145093993489353164033 12708108820495117014873025)
          ·
            refine ⟨9531081615371337761154769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12708108820495117014873025 9531081615371337761154769)
            ·
              refine ⟨7148311211528503320866077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9531081615371337761154769 7148311211528503320866077)
              ·
                refine ⟨2680616704323188745324779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7148311211528503320866077 2680616704323188745324779)
                ·
                  refine ⟨4020925056484783117987169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2680616704323188745324779 4020925056484783117987169)
                  ·
                    refine ⟨3015693792363587338490377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4020925056484783117987169 3015693792363587338490377)
                    ·
                      refine ⟨2261770344272690503867783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3015693792363587338490377 2261770344272690503867783)
                      ·
                        rfl

theorem cell23_4404782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 3, 1, 2, 2].length) (baseStart_4404782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4404782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4404782 prefixEnd_4404782 := by exact prefixLift 4404782
  have htrace : WordTrace (prefixWord ++ tailWord_4404782) baseStart_4404782 baseEnd_4404782 := by
    simpa [prefixWord, tailWord_4404782, baseEnd_4404782] using wordTrace_append hprefix tailTrace_4404782
  have hstable : (prefixWord ++ tailWord_4404782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4404782).length < 2 ^ (prefixWord ++ tailWord_4404782).sum := by decide
  have hdescent : baseEnd_4404782 < baseStart_4404782 := by decide
  rcases family_descends (prefixWord ++ tailWord_4404782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4404822 : List Nat := [5, 2, 2, 2, 2, 1, 2, 7]
def baseStart_4404822 : Nat := 118140960795 + 4404822 * 2 ^ 59
def prefixEnd_4404822 : Nat := 4983230072969 + 3 ^ 40 * 4404822 * 2
def baseEnd_4404822 : Nat := 83770032722180383235837

theorem tailTrace_4404822 : CollatzResearch.WordTrace tailWord_4404822 prefixEnd_4404822 83770032722180383235837 := by
  unfold tailWord_4404822
  simp only [CollatzResearch.WordTrace]
  refine ⟨10041066053005603284396545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 107104704565393101700229813 10041066053005603284396545)
  ·
    refine ⟨7530799539754202463297409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10041066053005603284396545 7530799539754202463297409)
    ·
      refine ⟨5648099654815651847473057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7530799539754202463297409 5648099654815651847473057)
      ·
        refine ⟨4236074741111738885604793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5648099654815651847473057 4236074741111738885604793)
        ·
          refine ⟨3177056055833804164203595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4236074741111738885604793 3177056055833804164203595)
          ·
            refine ⟨4765584083750706246305393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3177056055833804164203595 4765584083750706246305393)
            ·
              refine ⟨3574188062813029684729045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4765584083750706246305393 3574188062813029684729045)
              ·
                refine ⟨83770032722180383235837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3574188062813029684729045 83770032722180383235837)
                ·
                  rfl

theorem cell23_4404822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 2, 7].length) (baseStart_4404822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4404822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4404822 prefixEnd_4404822 := by exact prefixLift 4404822
  have htrace : WordTrace (prefixWord ++ tailWord_4404822) baseStart_4404822 baseEnd_4404822 := by
    simpa [prefixWord, tailWord_4404822, baseEnd_4404822] using wordTrace_append hprefix tailTrace_4404822
  have hstable : (prefixWord ++ tailWord_4404822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4404822).length < 2 ^ (prefixWord ++ tailWord_4404822).sum := by decide
  have hdescent : baseEnd_4404822 < baseStart_4404822 := by decide
  rcases family_descends (prefixWord ++ tailWord_4404822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4404861 : List Nat := [1, 4, 1, 1, 4, 3, 1, 1, 7]
def baseStart_4404861 : Nat := 118140960795 + 4404861 * 2 ^ 59
def prefixEnd_4404861 : Nat := 4983230072969 + 3 ^ 40 * 4404861 * 2
def baseEnd_4404861 : Nat := 251312323249377299419991

theorem tailTrace_4404861 : CollatzResearch.WordTrace tailWord_4404861 prefixEnd_4404861 251312323249377299419991 := by
  unfold tailWord_4404861
  simp only [CollatzResearch.WordTrace]
  refine ⟨160658479294948362211014437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107105652863298908140676291 160658479294948362211014437)
  ·
    refine ⟨30123464867802817914565207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 160658479294948362211014437 30123464867802817914565207)
    ·
      refine ⟨45185197301704226871847811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30123464867802817914565207 45185197301704226871847811)
      ·
        refine ⟨67777795952556340307771717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45185197301704226871847811 67777795952556340307771717)
        ·
          refine ⟨12708336741104313807707197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67777795952556340307771717 12708336741104313807707197)
          ·
            refine ⟨4765626277914117677890199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12708336741104313807707197 4765626277914117677890199)
            ·
              refine ⟨7148439416871176516835299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4765626277914117677890199 7148439416871176516835299)
              ·
                refine ⟨10722659125306764775252949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7148439416871176516835299 10722659125306764775252949)
                ·
                  refine ⟨251312323249377299419991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10722659125306764775252949 251312323249377299419991)
                  ·
                    rfl

theorem cell23_4404861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 1, 7].length) (baseStart_4404861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4404861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4404861 prefixEnd_4404861 := by exact prefixLift 4404861
  have htrace : WordTrace (prefixWord ++ tailWord_4404861) baseStart_4404861 baseEnd_4404861 := by
    simpa [prefixWord, tailWord_4404861, baseEnd_4404861] using wordTrace_append hprefix tailTrace_4404861
  have hstable : (prefixWord ++ tailWord_4404861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4404861).length < 2 ^ (prefixWord ++ tailWord_4404861).sum := by decide
  have hdescent : baseEnd_4404861 < baseStart_4404861 := by decide
  rcases family_descends (prefixWord ++ tailWord_4404861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4404872 : List Nat := [2, 1, 3, 5, 1, 1, 1, 3, 2, 2, 2]
def baseStart_4404872 : Nat := 118140960795 + 4404872 * 2 ^ 59
def prefixEnd_4404872 : Nat := 4983230072969 + 3 ^ 40 * 4404872 * 2
def baseEnd_4404872 : Nat := 2261816557531595151742369

theorem tailTrace_4404872 : CollatzResearch.WordTrace tailWord_4404872 prefixEnd_4404872 2261816557531595151742369 := by
  unfold tailWord_4404872
  simp only [CollatzResearch.WordTrace]
  refine ⟨80329440248954255544832435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107105920331939007393109913 80329440248954255544832435)
  ·
    refine ⟨120494160373431383317248653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80329440248954255544832435 120494160373431383317248653)
    ·
      refine ⟨45185310140036768743968245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120494160373431383317248653 45185310140036768743968245)
      ·
        refine ⟨4236122825628447069747023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45185310140036768743968245 4236122825628447069747023)
        ·
          refine ⟨6354184238442670604620535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4236122825628447069747023 6354184238442670604620535)
          ·
            refine ⟨9531276357664005906930803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6354184238442670604620535 9531276357664005906930803)
            ·
              refine ⟨14296914536496008860396205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9531276357664005906930803 14296914536496008860396205)
              ·
                refine ⟨5361342951186003322648577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14296914536496008860396205 5361342951186003322648577)
                ·
                  refine ⟨4021007213389502491986433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5361342951186003322648577 4021007213389502491986433)
                  ·
                    refine ⟨3015755410042126868989825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4021007213389502491986433 3015755410042126868989825)
                    ·
                      refine ⟨2261816557531595151742369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3015755410042126868989825 2261816557531595151742369)
                      ·
                        rfl

theorem cell23_4404872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_4404872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4404872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4404872 prefixEnd_4404872 := by exact prefixLift 4404872
  have htrace : WordTrace (prefixWord ++ tailWord_4404872) baseStart_4404872 baseEnd_4404872 := by
    simpa [prefixWord, tailWord_4404872, baseEnd_4404872] using wordTrace_append hprefix tailTrace_4404872
  have hstable : (prefixWord ++ tailWord_4404872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4404872).length < 2 ^ (prefixWord ++ tailWord_4404872).sum := by decide
  have hdescent : baseEnd_4404872 < baseStart_4404872 := by decide
  rcases family_descends (prefixWord ++ tailWord_4404872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4404911 : List Nat := [1, 1, 2, 1, 2, 4, 2, 2, 2, 4, 2]
def baseStart_4404911 : Nat := 118140960795 + 4404911 * 2 ^ 59
def prefixEnd_4404911 : Nat := 4983230072969 + 3 ^ 40 * 4404911 * 2
def baseEnd_4404911 : Nat := 2261836583277120499154689

theorem tailTrace_4404911 : CollatzResearch.WordTrace tailWord_4404911 prefixEnd_4404911 2261836583277120499154689 := by
  unfold tailWord_4404911
  simp only [CollatzResearch.WordTrace]
  refine ⟨160660302944767220750334587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107106868629844813833556391 160660302944767220750334587)
  ·
    refine ⟨240990454417150831125501881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160660302944767220750334587 240990454417150831125501881)
    ·
      refine ⟨180742840812863123344126411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 240990454417150831125501881 180742840812863123344126411)
      ·
        refine ⟨271114261219294685016189617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180742840812863123344126411 271114261219294685016189617)
        ·
          refine ⟨203335695914471013762142213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 271114261219294685016189617 203335695914471013762142213)
          ·
            refine ⟨38125442983963315080401665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 203335695914471013762142213 38125442983963315080401665)
            ·
              refine ⟨28594082237972486310301249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38125442983963315080401665 28594082237972486310301249)
              ·
                refine ⟨21445561678479364732725937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28594082237972486310301249 21445561678479364732725937)
                ·
                  refine ⟨16084171258859523549544453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21445561678479364732725937 16084171258859523549544453)
                  ·
                    refine ⟨3015782111036160665539585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16084171258859523549544453 3015782111036160665539585)
                    ·
                      refine ⟨2261836583277120499154689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3015782111036160665539585 2261836583277120499154689)
                      ·
                        rfl

theorem cell23_4404911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 2, 4, 2].length) (baseStart_4404911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4404911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4404911 prefixEnd_4404911 := by exact prefixLift 4404911
  have htrace : WordTrace (prefixWord ++ tailWord_4404911) baseStart_4404911 baseEnd_4404911 := by
    simpa [prefixWord, tailWord_4404911, baseEnd_4404911] using wordTrace_append hprefix tailTrace_4404911
  have hstable : (prefixWord ++ tailWord_4404911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4404911).length < 2 ^ (prefixWord ++ tailWord_4404911).sum := by decide
  have hdescent : baseEnd_4404911 < baseStart_4404911 := by decide
  rcases family_descends (prefixWord ++ tailWord_4404911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
