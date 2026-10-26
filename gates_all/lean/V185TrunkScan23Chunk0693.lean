import V185TrunkScan23Chunk0692

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4097786 : List Nat := [3, 1, 1, 1, 1, 3, 1, 2, 5, 1, 4]
def baseStart_4097786 : Nat := 118140960795 + 4097786 * 2 ^ 59
def prefixEnd_4097786 : Nat := 4983230072969 + 3 ^ 40 * 4097786 * 2
def baseEnd_4097786 : Nat := 2104133837265009627129631

theorem tailTrace_4097786 : CollatzResearch.WordTrace tailWord_4097786 prefixEnd_4097786 2104133837265009627129631 := by
  unfold tailWord_4097786
  simp only [CollatzResearch.WordTrace]
  refine ⟨37364633483107160744078303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99639022621619095317542141 37364633483107160744078303)
  ·
    refine ⟨56046950224660741116117455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37364633483107160744078303 56046950224660741116117455)
    ·
      refine ⟨84070425336991111674176183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56046950224660741116117455 84070425336991111674176183)
      ·
        refine ⟨126105638005486667511264275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84070425336991111674176183 126105638005486667511264275)
        ·
          refine ⟨189158457008230001266896413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126105638005486667511264275 189158457008230001266896413)
          ·
            refine ⟨70934421378086250475086155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189158457008230001266896413 70934421378086250475086155)
            ·
              refine ⟨106401632067129375712629233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70934421378086250475086155 106401632067129375712629233)
              ·
                refine ⟨79801224050347031784471925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106401632067129375712629233 79801224050347031784471925)
                ·
                  refine ⟨7481364754720034229794243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79801224050347031784471925 7481364754720034229794243)
                  ·
                    refine ⟨11222047132080051344691365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7481364754720034229794243 11222047132080051344691365)
                    ·
                      refine ⟨2104133837265009627129631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11222047132080051344691365 2104133837265009627129631)
                      ·
                        rfl

theorem cell23_4097786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 5, 1, 4].length) (baseStart_4097786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4097786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4097786 prefixEnd_4097786 := by exact prefixLift 4097786
  have htrace : WordTrace (prefixWord ++ tailWord_4097786) baseStart_4097786 baseEnd_4097786 := by
    simpa [prefixWord, tailWord_4097786, baseEnd_4097786] using wordTrace_append hprefix tailTrace_4097786
  have hstable : (prefixWord ++ tailWord_4097786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097786).length < 2 ^ (prefixWord ++ tailWord_4097786).sum := by decide
  have hdescent : baseEnd_4097786 < baseStart_4097786 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097816 : List Nat := [2, 1, 2, 3, 1, 1, 4, 1, 1, 1, 6]
def baseStart_4097816 : Nat := 118140960795 + 4097816 * 2 ^ 59
def prefixEnd_4097816 : Nat := 4983230072969 + 3 ^ 40 * 4097816 * 2
def baseEnd_4097816 : Nat := 2104149241684644509754493

theorem tailTrace_4097816 : CollatzResearch.WordTrace tailWord_4097816 prefixEnd_4097816 2104149241684644509754493 := by
  unfold tailWord_4097816
  simp only [CollatzResearch.WordTrace]
  refine ⟨74729814061159979049952651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99639752081546638733270201 74729814061159979049952651)
  ·
    refine ⟨112094721091739968574928977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74729814061159979049952651 112094721091739968574928977)
    ·
      refine ⟨84071040818804976431196733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112094721091739968574928977 84071040818804976431196733)
      ·
        refine ⟨31526640307051866161698775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84071040818804976431196733 31526640307051866161698775)
        ·
          refine ⟨47289960460577799242548163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31526640307051866161698775 47289960460577799242548163)
          ·
            refine ⟨70934940690866698863822245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47289960460577799242548163 70934940690866698863822245)
            ·
              refine ⟨13300301379537506036966671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70934940690866698863822245 13300301379537506036966671)
              ·
                refine ⟨19950452069306259055450007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13300301379537506036966671 19950452069306259055450007)
                ·
                  refine ⟨29925678103959388583175011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19950452069306259055450007 29925678103959388583175011)
                  ·
                    refine ⟨44888517155939082874762517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29925678103959388583175011 44888517155939082874762517)
                    ·
                      refine ⟨2104149241684644509754493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44888517155939082874762517 2104149241684644509754493)
                      ·
                        rfl

theorem cell23_4097816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_4097816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4097816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4097816 prefixEnd_4097816 := by exact prefixLift 4097816
  have htrace : WordTrace (prefixWord ++ tailWord_4097816) baseStart_4097816 baseEnd_4097816 := by
    simpa [prefixWord, tailWord_4097816, baseEnd_4097816] using wordTrace_append hprefix tailTrace_4097816
  have hstable : (prefixWord ++ tailWord_4097816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097816).length < 2 ^ (prefixWord ++ tailWord_4097816).sum := by decide
  have hdescent : baseEnd_4097816 < baseStart_4097816 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097820 : List Nat := [2, 2, 3, 1, 1, 2, 2, 1, 5, 2, 2]
def baseStart_4097820 : Nat := 118140960795 + 4097820 * 2 ^ 59
def prefixEnd_4097820 : Nat := 4983230072969 + 3 ^ 40 * 4097820 * 2
def baseEnd_4097820 : Nat := 2104151295607262494104475

theorem tailTrace_4097820 : CollatzResearch.WordTrace tailWord_4097820 prefixEnd_4097820 2104151295607262494104475 := by
  unfold tailWord_4097820
  simp only [CollatzResearch.WordTrace]
  refine ⟨74729887007152733391525457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99639849342870311188700609 74729887007152733391525457)
  ·
    refine ⟨56047415255364550043644093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74729887007152733391525457 56047415255364550043644093)
    ·
      refine ⟨21017780720761706266366535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56047415255364550043644093 21017780720761706266366535)
      ·
        refine ⟨31526671081142559399549803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21017780720761706266366535 31526671081142559399549803)
        ·
          refine ⟨47290006621713839099324705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31526671081142559399549803 47290006621713839099324705)
          ·
            refine ⟨35467504966285379324493529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47290006621713839099324705 35467504966285379324493529)
            ·
              refine ⟨26600628724714034493370147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35467504966285379324493529 26600628724714034493370147)
              ·
                refine ⟨39900943087071051740055221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26600628724714034493370147 39900943087071051740055221)
                ·
                  refine ⟨3740713414412911100630177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39900943087071051740055221 3740713414412911100630177)
                  ·
                    refine ⟨2805535060809683325472633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3740713414412911100630177 2805535060809683325472633)
                    ·
                      refine ⟨2104151295607262494104475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2805535060809683325472633 2104151295607262494104475)
                      ·
                        rfl

theorem cell23_4097820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 5, 2, 2].length) (baseStart_4097820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4097820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4097820 prefixEnd_4097820 := by exact prefixLift 4097820
  have htrace : WordTrace (prefixWord ++ tailWord_4097820) baseStart_4097820 baseEnd_4097820 := by
    simpa [prefixWord, tailWord_4097820, baseEnd_4097820] using wordTrace_append hprefix tailTrace_4097820
  have hstable : (prefixWord ++ tailWord_4097820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097820).length < 2 ^ (prefixWord ++ tailWord_4097820).sum := by decide
  have hdescent : baseEnd_4097820 < baseStart_4097820 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097823 : List Nat := [1, 1, 2, 4, 2, 1, 3, 1, 3, 2, 3]
def baseStart_4097823 : Nat := 118140960795 + 4097823 * 2 ^ 59
def prefixEnd_4097823 : Nat := 4983230072969 + 3 ^ 40 * 4097823 * 2
def baseEnd_4097823 : Nat := 2104152836049225982366961

theorem tailTrace_4097823 : CollatzResearch.WordTrace tailWord_4097823 prefixEnd_4097823 2104152836049225982366961 := by
  unfold tailWord_4097823
  simp only [CollatzResearch.WordTrace]
  refine ⟨149459883433294598295410123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99639922288863065530273415 149459883433294598295410123)
  ·
    refine ⟨224189825149941897443115185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149459883433294598295410123 224189825149941897443115185)
    ·
      refine ⟨168142368862456423082336389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224189825149941897443115185 168142368862456423082336389)
      ·
        refine ⟨31526694161710579327938073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168142368862456423082336389 31526694161710579327938073)
        ·
          refine ⟨23645020621282934495953555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31526694161710579327938073 23645020621282934495953555)
          ·
            refine ⟨35467530931924401743930333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23645020621282934495953555 35467530931924401743930333)
            ·
              refine ⟨13300324099471650653973875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35467530931924401743930333 13300324099471650653973875)
              ·
                refine ⟨19950486149207475980960813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13300324099471650653973875 19950486149207475980960813)
                ·
                  refine ⟨7481432305952803492860305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19950486149207475980960813 7481432305952803492860305)
                  ·
                    refine ⟨5611074229464602619645229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7481432305952803492860305 5611074229464602619645229)
                    ·
                      refine ⟨2104152836049225982366961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5611074229464602619645229 2104152836049225982366961)
                      ·
                        rfl

theorem cell23_4097823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 3, 2, 3].length) (baseStart_4097823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4097823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4097823 prefixEnd_4097823 := by exact prefixLift 4097823
  have htrace : WordTrace (prefixWord ++ tailWord_4097823) baseStart_4097823 baseEnd_4097823 := by
    simpa [prefixWord, tailWord_4097823, baseEnd_4097823] using wordTrace_append hprefix tailTrace_4097823
  have hstable : (prefixWord ++ tailWord_4097823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097823).length < 2 ^ (prefixWord ++ tailWord_4097823).sum := by decide
  have hdescent : baseEnd_4097823 < baseStart_4097823 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097826 : List Nat := [3, 3, 1, 1, 2, 1, 1, 11]
def baseStart_4097826 : Nat := 118140960795 + 4097826 * 2 ^ 59
def prefixEnd_4097826 : Nat := 4983230072969 + 3 ^ 40 * 4097826 * 2
def baseEnd_4097826 : Nat := 77931643573747758171461

theorem tailTrace_4097826 : CollatzResearch.WordTrace tailWord_4097826 prefixEnd_4097826 77931643573747758171461 := by
  unfold tailWord_4097826
  simp only [CollatzResearch.WordTrace]
  refine ⟨37364998213070932451942333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99639995234855819871846221 37364998213070932451942333)
  ·
    refine ⟨14011874329901599669478375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37364998213070932451942333 14011874329901599669478375)
    ·
      refine ⟨21017811494852399504217563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14011874329901599669478375 21017811494852399504217563)
      ·
        refine ⟨31526717242278599256326345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21017811494852399504217563 31526717242278599256326345)
        ·
          refine ⟨23645037931708949442244759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31526717242278599256326345 23645037931708949442244759)
          ·
            refine ⟨35467556897563424163367139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23645037931708949442244759 35467556897563424163367139)
            ·
              refine ⟨53201335346345136245050709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35467556897563424163367139 53201335346345136245050709)
              ·
                refine ⟨77931643573747758171461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 53201335346345136245050709 77931643573747758171461)
                ·
                  rfl

theorem cell23_4097826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 11].length) (baseStart_4097826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4097826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4097826 prefixEnd_4097826 := by exact prefixLift 4097826
  have htrace : WordTrace (prefixWord ++ tailWord_4097826) baseStart_4097826 baseEnd_4097826 := by
    simpa [prefixWord, tailWord_4097826, baseEnd_4097826] using wordTrace_append hprefix tailTrace_4097826
  have hstable : (prefixWord ++ tailWord_4097826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097826).length < 2 ^ (prefixWord ++ tailWord_4097826).sum := by decide
  have hdescent : baseEnd_4097826 < baseStart_4097826 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097921 : List Nat := [1, 2, 4, 4, 1, 1, 3, 1, 2, 1, 3]
def baseStart_4097921 : Nat := 118140960795 + 4097921 * 2 ^ 59
def prefixEnd_4097921 : Nat := 4983230072969 + 3 ^ 40 * 4097921 * 2
def baseEnd_4097921 : Nat := 2104203157153366598941511

theorem tailTrace_4097921 : CollatzResearch.WordTrace tailWord_4097921 prefixEnd_4097921 2104203157153366598941511 := by
  unfold tailWord_4097921
  simp only [CollatzResearch.WordTrace]
  refine ⟨149463457786939561032477617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99642305191293040688318411 149463457786939561032477617)
  ·
    refine ⟨112097593340204670774358213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149463457786939561032477617 112097593340204670774358213)
    ·
      refine ⟨21018298751288375770192165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112097593340204670774358213 21018298751288375770192165)
      ·
        refine ⟨3940931015866570456911031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21018298751288375770192165 3940931015866570456911031)
        ·
          refine ⟨5911396523799855685366547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3940931015866570456911031 5911396523799855685366547)
          ·
            refine ⟨8867094785699783528049821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5911396523799855685366547 8867094785699783528049821)
            ·
              refine ⟨3325160544637418823018683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8867094785699783528049821 3325160544637418823018683)
              ·
                refine ⟨4987740816956128234528025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3325160544637418823018683 4987740816956128234528025)
                ·
                  refine ⟨3740805612717096175896019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4987740816956128234528025 3740805612717096175896019)
                  ·
                    refine ⟨5611208419075644263844029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3740805612717096175896019 5611208419075644263844029)
                    ·
                      refine ⟨2104203157153366598941511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5611208419075644263844029 2104203157153366598941511)
                      ·
                        rfl

theorem cell23_4097921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_4097921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4097921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4097921 prefixEnd_4097921 := by exact prefixLift 4097921
  have htrace : WordTrace (prefixWord ++ tailWord_4097921) baseStart_4097921 baseEnd_4097921 := by
    simpa [prefixWord, tailWord_4097921, baseEnd_4097921] using wordTrace_append hprefix tailTrace_4097921
  have hstable : (prefixWord ++ tailWord_4097921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097921).length < 2 ^ (prefixWord ++ tailWord_4097921).sum := by decide
  have hdescent : baseEnd_4097921 < baseStart_4097921 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097923 : List Nat := [1, 1, 1, 3, 4, 2, 2, 1, 2, 2, 4]
def baseStart_4097923 : Nat := 118140960795 + 4097923 * 2 ^ 59
def prefixEnd_4097923 : Nat := 4983230072969 + 3 ^ 40 * 4097923 * 2
def baseEnd_4097923 : Nat := 2104204184114675591116501

theorem tailTrace_4097923 : CollatzResearch.WordTrace tailWord_4097923 prefixEnd_4097923 2104204184114675591116501 := by
  unfold tailWord_4097923
  simp only [CollatzResearch.WordTrace]
  refine ⟨149463530732932315374050423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99642353821954876916033615 149463530732932315374050423)
  ·
    refine ⟨224195296099398473061075635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149463530732932315374050423 224195296099398473061075635)
    ·
      refine ⟨336292944149097709591613453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224195296099398473061075635 336292944149097709591613453)
      ·
        refine ⟨126109854055911641096855045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 336292944149097709591613453 126109854055911641096855045)
        ·
          refine ⟨23645597635483432705660321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126109854055911641096855045 23645597635483432705660321)
          ·
            refine ⟨17734198226612574529245241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23645597635483432705660321 17734198226612574529245241)
            ·
              refine ⟨13300648669959430896933931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17734198226612574529245241 13300648669959430896933931)
              ·
                refine ⟨19950973004939146345400897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13300648669959430896933931 19950973004939146345400897)
                ·
                  refine ⟨14963229753704359759050673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19950973004939146345400897 14963229753704359759050673)
                  ·
                    refine ⟨11222422315278269819288005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14963229753704359759050673 11222422315278269819288005)
                    ·
                      refine ⟨2104204184114675591116501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11222422315278269819288005 2104204184114675591116501)
                      ·
                        rfl

theorem cell23_4097923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 2, 2, 4].length) (baseStart_4097923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4097923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4097923 prefixEnd_4097923 := by exact prefixLift 4097923
  have htrace : WordTrace (prefixWord ++ tailWord_4097923) baseStart_4097923 baseEnd_4097923 := by
    simpa [prefixWord, tailWord_4097923, baseEnd_4097923] using wordTrace_append hprefix tailTrace_4097923
  have hstable : (prefixWord ++ tailWord_4097923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097923).length < 2 ^ (prefixWord ++ tailWord_4097923).sum := by decide
  have hdescent : baseEnd_4097923 < baseStart_4097923 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097973 : List Nat := [1, 3, 3, 2, 1, 2, 1, 1, 1, 1, 7]
def baseStart_4097973 : Nat := 118140960795 + 4097973 * 2 ^ 59
def prefixEnd_4097973 : Nat := 4983230072969 + 3 ^ 40 * 4097973 * 2
def baseEnd_4097973 : Nat := 2104229858147400395491271

theorem tailTrace_4097973 : CollatzResearch.WordTrace tailWord_4097973 prefixEnd_4097973 2104229858147400395491271 := by
  unfold tailWord_4097973
  simp only [CollatzResearch.WordTrace]
  refine ⟨149465354382751173913370573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99643569588500782608913715 149465354382751173913370573)
  ·
    refine ⟨56049507893531690217513965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149465354382751173913370573 56049507893531690217513965)
    ·
      refine ⟨21018565460074383831567737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56049507893531690217513965 21018565460074383831567737)
      ·
        refine ⟨15763924095055787873675803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21018565460074383831567737 15763924095055787873675803)
        ·
          refine ⟨23645886142583681810513705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15763924095055787873675803 23645886142583681810513705)
          ·
            refine ⟨17734414606937761357885279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23645886142583681810513705 17734414606937761357885279)
            ·
              refine ⟨26601621910406642036827919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17734414606937761357885279 26601621910406642036827919)
              ·
                refine ⟨39902432865609963055241879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26601621910406642036827919 39902432865609963055241879)
                ·
                  refine ⟨59853649298414944582862819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39902432865609963055241879 59853649298414944582862819)
                  ·
                    refine ⟨89780473947622416874294229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59853649298414944582862819 89780473947622416874294229)
                    ·
                      refine ⟨2104229858147400395491271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 89780473947622416874294229 2104229858147400395491271)
                      ·
                        rfl

theorem cell23_4097973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_4097973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4097973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4097973 prefixEnd_4097973 := by exact prefixLift 4097973
  have htrace : WordTrace (prefixWord ++ tailWord_4097973) baseStart_4097973 baseEnd_4097973 := by
    simpa [prefixWord, tailWord_4097973, baseEnd_4097973] using wordTrace_append hprefix tailTrace_4097973
  have hstable : (prefixWord ++ tailWord_4097973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097973).length < 2 ^ (prefixWord ++ tailWord_4097973).sum := by decide
  have hdescent : baseEnd_4097973 < baseStart_4097973 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097983 : List Nat := [1, 1, 2, 2, 2, 1, 3, 2, 4, 1, 4]
def baseStart_4097983 : Nat := 118140960795 + 4097983 * 2 ^ 59
def prefixEnd_4097983 : Nat := 4983230072969 + 3 ^ 40 * 4097983 * 2
def baseEnd_4097983 : Nat := 2104234992953945356366225

theorem tailTrace_4097983 : CollatzResearch.WordTrace tailWord_4097983 prefixEnd_4097983 2104234992953945356366225 := by
  unfold tailWord_4097983
  simp only [CollatzResearch.WordTrace]
  refine ⟨149465719112714945621234603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99643812741809963747489735 149465719112714945621234603)
  ·
    refine ⟨224198578669072418431851905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149465719112714945621234603 224198578669072418431851905)
    ·
      refine ⟨168148934001804313823888929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224198578669072418431851905 168148934001804313823888929)
      ·
        refine ⟨126111700501353235367916697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168148934001804313823888929 126111700501353235367916697)
        ·
          refine ⟨94583775376014926525937523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126111700501353235367916697 94583775376014926525937523)
          ·
            refine ⟨141875663064022389788906285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94583775376014926525937523 141875663064022389788906285)
            ·
              refine ⟨53203373649008396170839857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141875663064022389788906285 53203373649008396170839857)
              ·
                refine ⟨39902530236756297128129893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53203373649008396170839857 39902530236756297128129893)
                ·
                  refine ⟨7481724419391805711524355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39902530236756297128129893 7481724419391805711524355)
                  ·
                    refine ⟨11222586629087708567286533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7481724419391805711524355 11222586629087708567286533)
                    ·
                      refine ⟨2104234992953945356366225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11222586629087708567286533 2104234992953945356366225)
                      ·
                        rfl

theorem cell23_4097983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 4, 1, 4].length) (baseStart_4097983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4097983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4097983 prefixEnd_4097983 := by exact prefixLift 4097983
  have htrace : WordTrace (prefixWord ++ tailWord_4097983) baseStart_4097983 baseEnd_4097983 := by
    simpa [prefixWord, tailWord_4097983, baseEnd_4097983] using wordTrace_append hprefix tailTrace_4097983
  have hstable : (prefixWord ++ tailWord_4097983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097983).length < 2 ^ (prefixWord ++ tailWord_4097983).sum := by decide
  have hdescent : baseEnd_4097983 < baseStart_4097983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098018 : List Nat := [3, 3, 3, 1, 3, 1, 2, 2, 5]
def baseStart_4098018 : Nat := 118140960795 + 4098018 * 2 ^ 59
def prefixEnd_4098018 : Nat := 4983230072969 + 3 ^ 40 * 4098018 * 2
def baseEnd_4098018 : Nat := 233805884975205857714285

theorem tailTrace_4098018 : CollatzResearch.WordTrace tailWord_4098018 prefixEnd_4098018 233805884975205857714285 := by
  unfold tailWord_4098018
  simp only [CollatzResearch.WordTrace]
  refine ⟨37366748916897036649689677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99644663778392097732505805 37366748916897036649689677)
  ·
    refine ⟨14012530843836388743633629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37366748916897036649689677 14012530843836388743633629)
    ·
      refine ⟨5254699066438645778862611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14012530843836388743633629 5254699066438645778862611)
      ·
        refine ⟨7882048599657968668293917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5254699066438645778862611 7882048599657968668293917)
        ·
          refine ⟨2955768224871738250610219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7882048599657968668293917 2955768224871738250610219)
          ·
            refine ⟨4433652337307607375915329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2955768224871738250610219 4433652337307607375915329)
            ·
              refine ⟨3325239252980705531936497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4433652337307607375915329 3325239252980705531936497)
              ·
                refine ⟨2493929439735529148952373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3325239252980705531936497 2493929439735529148952373)
                ·
                  refine ⟨233805884975205857714285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2493929439735529148952373 233805884975205857714285)
                  ·
                    rfl

theorem cell23_4098018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 2, 2, 5].length) (baseStart_4098018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4098018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4098018 prefixEnd_4098018 := by exact prefixLift 4098018
  have htrace : WordTrace (prefixWord ++ tailWord_4098018) baseStart_4098018 baseEnd_4098018 := by
    simpa [prefixWord, tailWord_4098018, baseEnd_4098018] using wordTrace_append hprefix tailTrace_4098018
  have hstable : (prefixWord ++ tailWord_4098018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098018).length < 2 ^ (prefixWord ++ tailWord_4098018).sum := by decide
  have hdescent : baseEnd_4098018 < baseStart_4098018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098020 : List Nat := [2, 3, 1, 1, 1, 1, 3, 4, 2, 2, 3]
def baseStart_4098020 : Nat := 118140960795 + 4098020 * 2 ^ 59
def prefixEnd_4098020 : Nat := 4983230072969 + 3 ^ 40 * 4098020 * 2
def baseEnd_4098020 : Nat := 2104253991738161711603555

theorem tailTrace_4098020 : CollatzResearch.WordTrace tailWord_4098020 prefixEnd_4098020 2104253991738161711603555 := by
  unfold tailWord_4098020
  simp only [CollatzResearch.WordTrace]
  refine ⟨74733534306790450470165757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99644712409053933960221009 74733534306790450470165757)
  ·
    refine ⟨28025075365046418926312159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74733534306790450470165757 28025075365046418926312159)
    ·
      refine ⟨42037613047569628389468239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28025075365046418926312159 42037613047569628389468239)
      ·
        refine ⟨63056419571354442584202359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42037613047569628389468239 63056419571354442584202359)
        ·
          refine ⟨94584629357031663876303539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63056419571354442584202359 94584629357031663876303539)
          ·
            refine ⟨141876944035547495814455309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94584629357031663876303539 141876944035547495814455309)
            ·
              refine ⟨53203854013330310930420741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141876944035547495814455309 53203854013330310930420741)
              ·
                refine ⟨9975722627499433299453889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53203854013330310930420741 9975722627499433299453889)
                ·
                  refine ⟨7481791970624574974590417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9975722627499433299453889 7481791970624574974590417)
                  ·
                    refine ⟨5611343977968431230942813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7481791970624574974590417 5611343977968431230942813)
                    ·
                      refine ⟨2104253991738161711603555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5611343977968431230942813 2104253991738161711603555)
                      ·
                        rfl

theorem cell23_4098020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 4, 2, 2, 3].length) (baseStart_4098020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4098020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4098020 prefixEnd_4098020 := by exact prefixLift 4098020
  have htrace : WordTrace (prefixWord ++ tailWord_4098020) baseStart_4098020 baseEnd_4098020 := by
    simpa [prefixWord, tailWord_4098020, baseEnd_4098020] using wordTrace_append hprefix tailTrace_4098020
  have hstable : (prefixWord ++ tailWord_4098020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098020).length < 2 ^ (prefixWord ++ tailWord_4098020).sum := by decide
  have hdescent : baseEnd_4098020 < baseStart_4098020 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098157 : List Nat := [1, 5, 1, 1, 2, 1, 2, 3, 1, 3, 3]
def baseStart_4098157 : Nat := 118140960795 + 4098157 * 2 ^ 59
def prefixEnd_4098157 : Nat := 4983230072969 + 3 ^ 40 * 4098157 * 2
def baseEnd_4098157 : Nat := 2104324338587827675590425

theorem tailTrace_4098157 : CollatzResearch.WordTrace tailWord_4098157 prefixEnd_4098157 2104324338587827675590425 := by
  unfold tailWord_4098157
  simp only [CollatzResearch.WordTrace]
  refine ⟨149472065414084573338068725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99648043609389715558712483 149472065414084573338068725)
  ·
    refine ⟨14013006132570428750443943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 149472065414084573338068725 14013006132570428750443943)
    ·
      refine ⟨21019509198855643125665915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14013006132570428750443943 21019509198855643125665915)
      ·
        refine ⟨31529263798283464688498873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21019509198855643125665915 31529263798283464688498873)
        ·
          refine ⟨23646947848712598516374155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31529263798283464688498873 23646947848712598516374155)
          ·
            refine ⟨35470421773068897774561233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23646947848712598516374155 35470421773068897774561233)
            ·
              refine ⟨26602816329801673330920925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35470421773068897774561233 26602816329801673330920925)
              ·
                refine ⟨9976056123675627499095347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26602816329801673330920925 9976056123675627499095347)
                ·
                  refine ⟨14964084185513441248643021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9976056123675627499095347 14964084185513441248643021)
                  ·
                    refine ⟨5611531569567540468241133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14964084185513441248643021 5611531569567540468241133)
                    ·
                      refine ⟨2104324338587827675590425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5611531569567540468241133 2104324338587827675590425)
                      ·
                        rfl

theorem cell23_4098157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 3, 1, 3, 3].length) (baseStart_4098157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4098157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4098157 prefixEnd_4098157 := by exact prefixLift 4098157
  have htrace : WordTrace (prefixWord ++ tailWord_4098157) baseStart_4098157 baseEnd_4098157 := by
    simpa [prefixWord, tailWord_4098157, baseEnd_4098157] using wordTrace_append hprefix tailTrace_4098157
  have hstable : (prefixWord ++ tailWord_4098157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098157).length < 2 ^ (prefixWord ++ tailWord_4098157).sum := by decide
  have hdescent : baseEnd_4098157 < baseStart_4098157 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098197 : List Nat := [1, 3, 2, 1, 1, 1, 3, 2, 3, 4, 2]
def baseStart_4098197 : Nat := 118140960795 + 4098197 * 2 ^ 59
def prefixEnd_4098197 : Nat := 4983230072969 + 3 ^ 40 * 4098197 * 2
def baseEnd_4098197 : Nat := 2104344877814007519090241

theorem tailTrace_4098197 : CollatzResearch.WordTrace tailWord_4098197 prefixEnd_4098197 2104344877814007519090241 := by
  unfold tailWord_4098197
  simp only [CollatzResearch.WordTrace]
  refine ⟨149473524333939660169524845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99649016222626440113016563 149473524333939660169524845)
  ·
    refine ⟨56052571625227372563571817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149473524333939660169524845 56052571625227372563571817)
    ·
      refine ⟨42039428718920529422678863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56052571625227372563571817 42039428718920529422678863)
      ·
        refine ⟨63059143078380794134018295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42039428718920529422678863 63059143078380794134018295)
        ·
          refine ⟨94588714617571191201027443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63059143078380794134018295 94588714617571191201027443)
          ·
            refine ⟨141883071926356786801541165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94588714617571191201027443 141883071926356786801541165)
            ·
              refine ⟨53206151972383795050577937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141883071926356786801541165 53206151972383795050577937)
              ·
                refine ⟨39904613979287846287933453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53206151972383795050577937 39904613979287846287933453)
                ·
                  refine ⟨14964230242232942357975045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39904613979287846287933453 14964230242232942357975045)
                  ·
                    refine ⟨2805793170418676692120321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14964230242232942357975045 2805793170418676692120321)
                    ·
                      refine ⟨2104344877814007519090241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2805793170418676692120321 2104344877814007519090241)
                      ·
                        rfl

theorem cell23_4098197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 3, 4, 2].length) (baseStart_4098197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4098197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4098197 prefixEnd_4098197 := by exact prefixLift 4098197
  have htrace : WordTrace (prefixWord ++ tailWord_4098197) baseStart_4098197 baseEnd_4098197 := by
    simpa [prefixWord, tailWord_4098197, baseEnd_4098197] using wordTrace_append hprefix tailTrace_4098197
  have hstable : (prefixWord ++ tailWord_4098197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098197).length < 2 ^ (prefixWord ++ tailWord_4098197).sum := by decide
  have hdescent : baseEnd_4098197 < baseStart_4098197 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098207 : List Nat := [1, 1, 2, 6, 1, 2, 1, 1, 2, 6]
def baseStart_4098207 : Nat := 118140960795 + 4098207 * 2 ^ 59
def prefixEnd_4098207 : Nat := 4983230072969 + 3 ^ 40 * 4098207 * 2
def baseEnd_4098207 : Nat := 701450004206850826655065

theorem tailTrace_4098207 : CollatzResearch.WordTrace tailWord_4098207 prefixEnd_4098207 701450004206850826655065 := by
  unfold tailWord_4098207
  simp only [CollatzResearch.WordTrace]
  refine ⟨149473889063903431877388875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99649259375935621251592583 149473889063903431877388875)
  ·
    refine ⟨224210833595855147816083313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149473889063903431877388875 224210833595855147816083313)
    ·
      refine ⟨168158125196891360862062485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224210833595855147816083313 168158125196891360862062485)
      ·
        refine ⟨7882412118604282540409179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 168158125196891360862062485 7882412118604282540409179)
        ·
          refine ⟨11823618177906423810613769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7882412118604282540409179 11823618177906423810613769)
          ·
            refine ⟨8867713633429817857960327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11823618177906423810613769 8867713633429817857960327)
            ·
              refine ⟨13301570450144726786940491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8867713633429817857960327 13301570450144726786940491)
              ·
                refine ⟨19952355675217090180410737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13301570450144726786940491 19952355675217090180410737)
                ·
                  refine ⟨14964266756412817635308053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19952355675217090180410737 14964266756412817635308053)
                  ·
                    refine ⟨701450004206850826655065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14964266756412817635308053 701450004206850826655065)
                    ·
                      rfl

theorem cell23_4098207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 2, 6].length) (baseStart_4098207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4098207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4098207 prefixEnd_4098207 := by exact prefixLift 4098207
  have htrace : WordTrace (prefixWord ++ tailWord_4098207) baseStart_4098207 baseEnd_4098207 := by
    simpa [prefixWord, tailWord_4098207, baseEnd_4098207] using wordTrace_append hprefix tailTrace_4098207
  have hstable : (prefixWord ++ tailWord_4098207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098207).length < 2 ^ (prefixWord ++ tailWord_4098207).sum := by decide
  have hdescent : baseEnd_4098207 < baseStart_4098207 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098254 : List Nat := [4, 1, 1, 1, 4, 1, 2, 4, 5]
def baseStart_4098254 : Nat := 118140960795 + 4098254 * 2 ^ 59
def prefixEnd_4098254 : Nat := 4983230072969 + 3 ^ 40 * 4098254 * 2
def baseEnd_4098254 : Nat := 233819349579034866230831

theorem tailTrace_4098254 : CollatzResearch.WordTrace tailWord_4098254 prefixEnd_4098254 233819349579034866230831 := by
  unfold tailWord_4098254
  simp only [CollatzResearch.WordTrace]
  refine ⟨18684450411841644863043727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99650402196488772602899877 18684450411841644863043727)
  ·
    refine ⟨28026675617762467294565591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18684450411841644863043727 28026675617762467294565591)
    ·
      refine ⟨42040013426643700941848387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28026675617762467294565591 42040013426643700941848387)
      ·
        refine ⟨63060020139965551412772581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42040013426643700941848387 63060020139965551412772581)
        ·
          refine ⟨11823753776243540889894859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63060020139965551412772581 11823753776243540889894859)
          ·
            refine ⟨17735630664365311334842289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11823753776243540889894859 17735630664365311334842289)
            ·
              refine ⟨13301722998273983501131717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17735630664365311334842289 13301722998273983501131717)
              ·
                refine ⟨2494073062176371906462197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13301722998273983501131717 2494073062176371906462197)
                ·
                  refine ⟨233819349579034866230831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2494073062176371906462197 233819349579034866230831)
                  ·
                    rfl

theorem cell23_4098254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 4, 5].length) (baseStart_4098254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4098254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4098254 prefixEnd_4098254 := by exact prefixLift 4098254
  have htrace : WordTrace (prefixWord ++ tailWord_4098254) baseStart_4098254 baseEnd_4098254 := by
    simpa [prefixWord, tailWord_4098254, baseEnd_4098254] using wordTrace_append hprefix tailTrace_4098254
  have hstable : (prefixWord ++ tailWord_4098254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098254).length < 2 ^ (prefixWord ++ tailWord_4098254).sum := by decide
  have hdescent : baseEnd_4098254 < baseStart_4098254 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098257 : List Nat := [1, 2, 2, 1, 2, 2, 2, 1, 1, 7, 2]
def baseStart_4098257 : Nat := 118140960795 + 4098257 * 2 ^ 59
def prefixEnd_4098257 : Nat := 4983230072969 + 3 ^ 40 * 4098257 * 2
def baseEnd_4098257 : Nat := 2104375686653277284339965

theorem tailTrace_4098257 : CollatzResearch.WordTrace tailWord_4098257 prefixEnd_4098257 2104375686653277284339965 := by
  unfold tailWord_4098257
  simp only [CollatzResearch.WordTrace]
  refine ⟨149475712713722290416709025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99650475142481526944472683 149475712713722290416709025)
  ·
    refine ⟨112106784535291717812531769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149475712713722290416709025 112106784535291717812531769)
    ·
      refine ⟨84080088401468788359398827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112106784535291717812531769 84080088401468788359398827)
      ·
        refine ⟨126120132602203182539098241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84080088401468788359398827 126120132602203182539098241)
        ·
          refine ⟨94590099451652386904323681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126120132602203182539098241 94590099451652386904323681)
          ·
            refine ⟨70942574588739290178242761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94590099451652386904323681 70942574588739290178242761)
            ·
              refine ⟨53206930941554467633682071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70942574588739290178242761 53206930941554467633682071)
              ·
                refine ⟨79810396412331701450523107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53206930941554467633682071 79810396412331701450523107)
                ·
                  refine ⟨119715594618497552175784661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79810396412331701450523107 119715594618497552175784661)
                  ·
                    refine ⟨2805834248871036379119953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 119715594618497552175784661 2805834248871036379119953)
                    ·
                      refine ⟨2104375686653277284339965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2805834248871036379119953 2104375686653277284339965)
                      ·
                        rfl

theorem cell23_4098257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 7, 2].length) (baseStart_4098257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4098257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4098257 prefixEnd_4098257 := by exact prefixLift 4098257
  have htrace : WordTrace (prefixWord ++ tailWord_4098257) baseStart_4098257 baseEnd_4098257 := by
    simpa [prefixWord, tailWord_4098257, baseEnd_4098257] using wordTrace_append hprefix tailTrace_4098257
  have hstable : (prefixWord ++ tailWord_4098257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098257).length < 2 ^ (prefixWord ++ tailWord_4098257).sum := by decide
  have hdescent : baseEnd_4098257 < baseStart_4098257 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098287 : List Nat := [1, 1, 2, 1, 6, 1, 2, 1, 1, 3, 4]
def baseStart_4098287 : Nat := 118140960795 + 4098287 * 2 ^ 59
def prefixEnd_4098287 : Nat := 4983230072969 + 3 ^ 40 * 4098287 * 2
def baseEnd_4098287 : Nat := 2104391091072912166964827

theorem tailTrace_4098287 : CollatzResearch.WordTrace tailWord_4098287 prefixEnd_4098287 2104391091072912166964827 := by
  unfold tailWord_4098287
  simp only [CollatzResearch.WordTrace]
  refine ⟨149476806903613605540301115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99651204602409070360200743 149476806903613605540301115)
  ·
    refine ⟨224215210355420408310451673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149476806903613605540301115 224215210355420408310451673)
    ·
      refine ⟨168161407766565306232838755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224215210355420408310451673 168161407766565306232838755)
      ·
        refine ⟨252242111649847959349258133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168161407766565306232838755 252242111649847959349258133)
        ·
          refine ⟨11823848983586623094496475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 252242111649847959349258133 11823848983586623094496475)
          ·
            refine ⟨17735773475379934641744713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11823848983586623094496475 17735773475379934641744713)
            ·
              refine ⟨13301830106534950981308535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17735773475379934641744713 13301830106534950981308535)
              ·
                refine ⟨19952745159802426471962803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13301830106534950981308535 19952745159802426471962803)
                ·
                  refine ⟨29929117739703639707944205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19952745159802426471962803 29929117739703639707944205)
                  ·
                    refine ⟨11223419152388864890479077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29929117739703639707944205 11223419152388864890479077)
                    ·
                      refine ⟨2104391091072912166964827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11223419152388864890479077 2104391091072912166964827)
                      ·
                        rfl

theorem cell23_4098287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 3, 4].length) (baseStart_4098287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4098287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4098287 prefixEnd_4098287 := by exact prefixLift 4098287
  have htrace : WordTrace (prefixWord ++ tailWord_4098287) baseStart_4098287 baseEnd_4098287 := by
    simpa [prefixWord, tailWord_4098287, baseEnd_4098287] using wordTrace_append hprefix tailTrace_4098287
  have hstable : (prefixWord ++ tailWord_4098287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098287).length < 2 ^ (prefixWord ++ tailWord_4098287).sum := by decide
  have hdescent : baseEnd_4098287 < baseStart_4098287 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098314 : List Nat := [3, 1, 2, 2, 1, 1, 5, 1, 3, 4]
def baseStart_4098314 : Nat := 118140960795 + 4098314 * 2 ^ 59
def prefixEnd_4098314 : Nat := 4983230072969 + 3 ^ 40 * 4098314 * 2
def baseEnd_4098314 : Nat := 701468318350194520442401

theorem tailTrace_4098314 : CollatzResearch.WordTrace tailWord_4098314 prefixEnd_4098314 701468318350194520442401 := by
  unfold tailWord_4098314
  simp only [CollatzResearch.WordTrace]
  refine ⟨37369447918628947287883499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99651861116343859434355997 37369447918628947287883499)
  ·
    refine ⟨56054171877943420931825249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37369447918628947287883499 56054171877943420931825249)
    ·
      refine ⟨42040628908457565698868937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56054171877943420931825249 42040628908457565698868937)
      ·
        refine ⟨31530471681343174274151703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42040628908457565698868937 31530471681343174274151703)
        ·
          refine ⟨47295707522014761411227555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31530471681343174274151703 47295707522014761411227555)
          ·
            refine ⟨70943561283022142116841333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47295707522014761411227555 70943561283022142116841333)
            ·
              refine ⟨6650958870283325823453875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70943561283022142116841333 6650958870283325823453875)
              ·
                refine ⟨9976438305424988735180813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6650958870283325823453875 9976438305424988735180813)
                ·
                  refine ⟨3741164364534370775692805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9976438305424988735180813 3741164364534370775692805)
                  ·
                    refine ⟨701468318350194520442401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3741164364534370775692805 701468318350194520442401)
                    ·
                      rfl

theorem cell23_4098314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 1, 3, 4].length) (baseStart_4098314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4098314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4098314 prefixEnd_4098314 := by exact prefixLift 4098314
  have htrace : WordTrace (prefixWord ++ tailWord_4098314) baseStart_4098314 baseEnd_4098314 := by
    simpa [prefixWord, tailWord_4098314, baseEnd_4098314] using wordTrace_append hprefix tailTrace_4098314
  have hstable : (prefixWord ++ tailWord_4098314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098314).length < 2 ^ (prefixWord ++ tailWord_4098314).sum := by decide
  have hdescent : baseEnd_4098314 < baseStart_4098314 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098337 : List Nat := [1, 2, 3, 2, 1, 1, 2, 1, 2, 5, 3]
def baseStart_4098337 : Nat := 118140960795 + 4098337 * 2 ^ 59
def prefixEnd_4098337 : Nat := 4983230072969 + 3 ^ 40 * 4098337 * 2
def baseEnd_4098337 : Nat := 2104416765105636971339597

theorem tailTrace_4098337 : CollatzResearch.WordTrace tailWord_4098337 prefixEnd_4098337 2104416765105636971339597 := by
  unfold tailWord_4098337
  simp only [CollatzResearch.WordTrace]
  refine ⟨149478630553432464079621265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99652420368954976053080843 149478630553432464079621265)
  ·
    refine ⟨112108972915074348059715949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149478630553432464079621265 112108972915074348059715949)
    ·
      refine ⟨42040864843152880522393481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112108972915074348059715949 42040864843152880522393481)
      ·
        refine ⟨31530648632364660391795111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42040864843152880522393481 31530648632364660391795111)
        ·
          refine ⟨47295972948546990587692667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31530648632364660391795111 47295972948546990587692667)
          ·
            refine ⟨70943959422820485881539001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47295972948546990587692667 70943959422820485881539001)
            ·
              refine ⟨53207969567115364411154251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70943959422820485881539001 53207969567115364411154251)
              ·
                refine ⟨79811954350673046616731377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53207969567115364411154251 79811954350673046616731377)
                ·
                  refine ⟨59858965763004784962548533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79811954350673046616731377 59858965763004784962548533)
                  ·
                    refine ⟨5611778040281698590238925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59858965763004784962548533 5611778040281698590238925)
                    ·
                      refine ⟨2104416765105636971339597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5611778040281698590238925 2104416765105636971339597)
                      ·
                        rfl

theorem cell23_4098337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 5, 3].length) (baseStart_4098337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4098337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4098337 prefixEnd_4098337 := by exact prefixLift 4098337
  have htrace : WordTrace (prefixWord ++ tailWord_4098337) baseStart_4098337 baseEnd_4098337 := by
    simpa [prefixWord, tailWord_4098337, baseEnd_4098337] using wordTrace_append hprefix tailTrace_4098337
  have hstable : (prefixWord ++ tailWord_4098337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098337).length < 2 ^ (prefixWord ++ tailWord_4098337).sum := by decide
  have hdescent : baseEnd_4098337 < baseStart_4098337 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098341 : List Nat := [1, 3, 1, 2, 5, 1, 2, 1, 2, 2, 3]
def baseStart_4098341 : Nat := 118140960795 + 4098341 * 2 ^ 59
def prefixEnd_4098341 : Nat := 4983230072969 + 3 ^ 40 * 4098341 * 2
def baseEnd_4098341 : Nat := 2104418819028254955689579

theorem tailTrace_4098341 : CollatzResearch.WordTrace tailWord_4098341 prefixEnd_4098341 2104418819028254955689579 := by
  unfold tailWord_4098341
  simp only [CollatzResearch.WordTrace]
  refine ⟨149478776445417972762766877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99652517630278648508511251 149478776445417972762766877)
  ·
    refine ⟨56054541167031739786037579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149478776445417972762766877 56054541167031739786037579)
    ·
      refine ⟨84081811750547609679056369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56054541167031739786037579 84081811750547609679056369)
      ·
        refine ⟨63061358812910707259292277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84081811750547609679056369 63061358812910707259292277)
        ·
          refine ⟨5912002388710378805558651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63061358812910707259292277 5912002388710378805558651)
          ·
            refine ⟨8868003583065568208337977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5912002388710378805558651 8868003583065568208337977)
            ·
              refine ⟨6651002687299176156253483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8868003583065568208337977 6651002687299176156253483)
              ·
                refine ⟨9976504030948764234380225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6651002687299176156253483 9976504030948764234380225)
                ·
                  refine ⟨7482378023211573175785169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9976504030948764234380225 7482378023211573175785169)
                  ·
                    refine ⟨5611783517408679881838877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7482378023211573175785169 5611783517408679881838877)
                    ·
                      refine ⟨2104418819028254955689579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5611783517408679881838877 2104418819028254955689579)
                      ·
                        rfl

theorem cell23_4098341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 1, 2, 2, 3].length) (baseStart_4098341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4098341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4098341 prefixEnd_4098341 := by exact prefixLift 4098341
  have htrace : WordTrace (prefixWord ++ tailWord_4098341) baseStart_4098341 baseEnd_4098341 := by
    simpa [prefixWord, tailWord_4098341, baseEnd_4098341] using wordTrace_append hprefix tailTrace_4098341
  have hstable : (prefixWord ++ tailWord_4098341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098341).length < 2 ^ (prefixWord ++ tailWord_4098341).sum := by decide
  have hdescent : baseEnd_4098341 < baseStart_4098341 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098394 : List Nat := [3, 1, 1, 2, 1, 2, 1, 6, 1, 1, 4]
def baseStart_4098394 : Nat := 118140960795 + 4098394 * 2 ^ 59
def prefixEnd_4098394 : Nat := 4983230072969 + 3 ^ 40 * 4098394 * 2
def baseEnd_4098394 : Nat := 2104446033502943248326835

theorem tailTrace_4098394 : CollatzResearch.WordTrace tailWord_4098394 prefixEnd_4098394 2104446033502943248326835 := by
  unfold tailWord_4098394
  simp only [CollatzResearch.WordTrace]
  refine ⟨37370177378556490703611559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99653806342817308542964157 37370177378556490703611559)
  ·
    refine ⟨56055266067834736055417339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37370177378556490703611559 56055266067834736055417339)
    ·
      refine ⟨84082899101752104083126009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56055266067834736055417339 84082899101752104083126009)
      ·
        refine ⟨63062174326314078062344507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84082899101752104083126009 63062174326314078062344507)
        ·
          refine ⟨94593261489471117093516761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63062174326314078062344507 94593261489471117093516761)
          ·
            refine ⟨70944946117103337820137571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94593261489471117093516761 70944946117103337820137571)
            ·
              refine ⟨106417419175655006730206357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70944946117103337820137571 106417419175655006730206357)
              ·
                refine ⟨4988316523858828440478423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 106417419175655006730206357 4988316523858828440478423)
                ·
                  refine ⟨7482474785788242660717635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4988316523858828440478423 7482474785788242660717635)
                  ·
                    refine ⟨11223712178682363991076453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7482474785788242660717635 11223712178682363991076453)
                    ·
                      refine ⟨2104446033502943248326835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11223712178682363991076453 2104446033502943248326835)
                      ·
                        rfl

theorem cell23_4098394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 6, 1, 1, 4].length) (baseStart_4098394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4098394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4098394 prefixEnd_4098394 := by exact prefixLift 4098394
  have htrace : WordTrace (prefixWord ++ tailWord_4098394) baseStart_4098394 baseEnd_4098394 := by
    simpa [prefixWord, tailWord_4098394, baseEnd_4098394] using wordTrace_append hprefix tailTrace_4098394
  have hstable : (prefixWord ++ tailWord_4098394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098394).length < 2 ^ (prefixWord ++ tailWord_4098394).sum := by decide
  have hdescent : baseEnd_4098394 < baseStart_4098394 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098404 : List Nat := [2, 3, 1, 1, 3, 1, 2, 2, 4, 4]
def baseStart_4098404 : Nat := 118140960795 + 4098404 * 2 ^ 59
def prefixEnd_4098404 : Nat := 4983230072969 + 3 ^ 40 * 4098404 * 2
def baseEnd_4098404 : Nat := 701483722769829403067263

theorem tailTrace_4098404 : CollatzResearch.WordTrace tailWord_4098404 prefixEnd_4098404 701483722769829403067263 := by
  unfold tailWord_4098404
  simp only [CollatzResearch.WordTrace]
  refine ⟨74740537122094867261155133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99654049496126489681540177 74740537122094867261155133)
  ·
    refine ⟨28027701420785575222933175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74740537122094867261155133 28027701420785575222933175)
    ·
      refine ⟨42041552131178362834399763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28027701420785575222933175 42041552131178362834399763)
      ·
        refine ⟨63062328196767544251599645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42041552131178362834399763 63062328196767544251599645)
        ·
          refine ⟨23648373073787829094349867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63062328196767544251599645 23648373073787829094349867)
          ·
            refine ⟨35472559610681743641524801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23648373073787829094349867 35472559610681743641524801)
            ·
              refine ⟨26604419708011307731143601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35472559610681743641524801 26604419708011307731143601)
              ·
                refine ⟨19953314781008480798357701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26604419708011307731143601 19953314781008480798357701)
                ·
                  refine ⟨3741246521439090149692069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19953314781008480798357701 3741246521439090149692069)
                  ·
                    refine ⟨701483722769829403067263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3741246521439090149692069 701483722769829403067263)
                    ·
                      rfl

theorem cell23_4098404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 4, 4].length) (baseStart_4098404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4098404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4098404 prefixEnd_4098404 := by exact prefixLift 4098404
  have htrace : WordTrace (prefixWord ++ tailWord_4098404) baseStart_4098404 baseEnd_4098404 := by
    simpa [prefixWord, tailWord_4098404, baseEnd_4098404] using wordTrace_append hprefix tailTrace_4098404
  have hstable : (prefixWord ++ tailWord_4098404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098404).length < 2 ^ (prefixWord ++ tailWord_4098404).sum := by decide
  have hdescent : baseEnd_4098404 < baseStart_4098404 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098408 : List Nat := [2, 1, 4, 2, 2, 3, 2, 1, 1, 5]
def baseStart_4098408 : Nat := 118140960795 + 4098408 * 2 ^ 59
def prefixEnd_4098408 : Nat := 4983230072969 + 3 ^ 40 * 4098408 * 2
def baseEnd_4098408 : Nat := 701484407410702064517257

theorem tailTrace_4098408 : CollatzResearch.WordTrace tailWord_4098408 prefixEnd_4098408 701484407410702064517257 := by
  unfold tailWord_4098408
  simp only [CollatzResearch.WordTrace]
  refine ⟨74740610068087621602727939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99654146757450162136970585 74740610068087621602727939)
  ·
    refine ⟨112110915102131432404091909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74740610068087621602727939 112110915102131432404091909)
    ·
      refine ⟨21020796581649643575767233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112110915102131432404091909 21020796581649643575767233)
      ·
        refine ⟨15765597436237232681825425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21020796581649643575767233 15765597436237232681825425)
        ·
          refine ⟨11824198077177924511369069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15765597436237232681825425 11824198077177924511369069)
          ·
            refine ⟨4434074278941721691763401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11824198077177924511369069 4434074278941721691763401)
            ·
              refine ⟨3325555709206291268822551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4434074278941721691763401 3325555709206291268822551)
              ·
                refine ⟨4988333563809436903233827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3325555709206291268822551 4988333563809436903233827)
                ·
                  refine ⟨7482500345714155354850741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4988333563809436903233827 7482500345714155354850741)
                  ·
                    refine ⟨701484407410702064517257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7482500345714155354850741 701484407410702064517257)
                    ·
                      rfl

theorem cell23_4098408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 2, 1, 1, 5].length) (baseStart_4098408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4098408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4098408 prefixEnd_4098408 := by exact prefixLift 4098408
  have htrace : WordTrace (prefixWord ++ tailWord_4098408) baseStart_4098408 baseEnd_4098408 := by
    simpa [prefixWord, tailWord_4098408, baseEnd_4098408] using wordTrace_append hprefix tailTrace_4098408
  have hstable : (prefixWord ++ tailWord_4098408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098408).length < 2 ^ (prefixWord ++ tailWord_4098408).sum := by decide
  have hdescent : baseEnd_4098408 < baseStart_4098408 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098421 : List Nat := [1, 3, 4, 1, 2, 2, 1, 1, 4, 4]
def baseStart_4098421 : Nat := 118140960795 + 4098421 * 2 ^ 59
def prefixEnd_4098421 : Nat := 4983230072969 + 3 ^ 40 * 4098421 * 2
def baseEnd_4098421 : Nat := 701486632493538214229737

theorem tailTrace_4098421 : CollatzResearch.WordTrace tailWord_4098421 prefixEnd_4098421 701486632493538214229737 := by
  unfold tailWord_4098421
  simp only [CollatzResearch.WordTrace]
  refine ⟨149481694285128146425679117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99654462856752097617119411 149481694285128146425679117)
  ·
    refine ⟨56055635356923054909629669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149481694285128146425679117 56055635356923054909629669)
    ·
      refine ⟨10510431629423072795555563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56055635356923054909629669 10510431629423072795555563)
      ·
        refine ⟨15765647444134609193333345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10510431629423072795555563 15765647444134609193333345)
        ·
          refine ⟨11824235583100956895000009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15765647444134609193333345 11824235583100956895000009)
          ·
            refine ⟨8868176687325717671250007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11824235583100956895000009 8868176687325717671250007)
            ·
              refine ⟨13302265030988576506875011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8868176687325717671250007 13302265030988576506875011)
              ·
                refine ⟨19953397546482864760312517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13302265030988576506875011 19953397546482864760312517)
                ·
                  refine ⟨3741262039965537142558597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19953397546482864760312517 3741262039965537142558597)
                  ·
                    refine ⟨701486632493538214229737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3741262039965537142558597 701486632493538214229737)
                    ·
                      rfl

theorem cell23_4098421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_4098421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4098421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4098421 prefixEnd_4098421 := by exact prefixLift 4098421
  have htrace : WordTrace (prefixWord ++ tailWord_4098421) baseStart_4098421 baseEnd_4098421 := by
    simpa [prefixWord, tailWord_4098421, baseEnd_4098421] using wordTrace_append hprefix tailTrace_4098421
  have hstable : (prefixWord ++ tailWord_4098421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098421).length < 2 ^ (prefixWord ++ tailWord_4098421).sum := by decide
  have hdescent : baseEnd_4098421 < baseStart_4098421 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098441 : List Nat := [1, 2, 1, 1, 6, 3, 1, 1, 1, 2, 4]
def baseStart_4098441 : Nat := 118140960795 + 4098441 * 2 ^ 59
def prefixEnd_4098441 : Nat := 4983230072969 + 3 ^ 40 * 4098441 * 2
def baseEnd_4098441 : Nat := 2104470167093704564439119

theorem tailTrace_4098441 : CollatzResearch.WordTrace tailWord_4098441 prefixEnd_4098441 2104470167093704564439119 := by
  unfold tailWord_4098441
  simp only [CollatzResearch.WordTrace]
  refine ⟨149482423745055689841407177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99654949163370459894271451 149482423745055689841407177)
  ·
    refine ⟨112111817808791767381055383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149482423745055689841407177 112111817808791767381055383)
    ·
      refine ⟨168167726713187651071583075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112111817808791767381055383 168167726713187651071583075)
      ·
        refine ⟨252251590069781476607374613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168167726713187651071583075 252251590069781476607374613)
        ·
          refine ⟨11824293284521006715970685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 252251590069781476607374613 11824293284521006715970685)
          ·
            refine ⟨4434109981695377518489007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11824293284521006715970685 4434109981695377518489007)
            ·
              refine ⟨6651164972543066277733511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4434109981695377518489007 6651164972543066277733511)
              ·
                refine ⟨9976747458814599416600267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6651164972543066277733511 9976747458814599416600267)
                ·
                  refine ⟨14965121188221899124900401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9976747458814599416600267 14965121188221899124900401)
                  ·
                    refine ⟨11223840891166424343675301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14965121188221899124900401 11223840891166424343675301)
                    ·
                      refine ⟨2104470167093704564439119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11223840891166424343675301 2104470167093704564439119)
                      ·
                        rfl

theorem cell23_4098441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 1, 1, 2, 4].length) (baseStart_4098441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4098441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4098441 prefixEnd_4098441 := by exact prefixLift 4098441
  have htrace : WordTrace (prefixWord ++ tailWord_4098441) baseStart_4098441 baseEnd_4098441 := by
    simpa [prefixWord, tailWord_4098441, baseEnd_4098441] using wordTrace_append hprefix tailTrace_4098441
  have hstable : (prefixWord ++ tailWord_4098441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098441).length < 2 ^ (prefixWord ++ tailWord_4098441).sum := by decide
  have hdescent : baseEnd_4098441 < baseStart_4098441 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098457 : List Nat := [1, 2, 1, 2, 1, 4, 1, 1, 1, 4, 5]
def baseStart_4098457 : Nat := 118140960795 + 4098457 * 2 ^ 59
def prefixEnd_4098457 : Nat := 4983230072969 + 3 ^ 40 * 4098457 * 2
def baseEnd_4098457 : Nat := 2104478382784176501839045

theorem tailTrace_4098457 : CollatzResearch.WordTrace tailWord_4098457 prefixEnd_4098457 2104478382784176501839045 := by
  unfold tailWord_4098457
  simp only [CollatzResearch.WordTrace]
  refine ⟨149483007312997724573989625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99655338208665149715993083 149483007312997724573989625)
  ·
    refine ⟨112112255484748293430492219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149483007312997724573989625 112112255484748293430492219)
    ·
      refine ⟨168168383227122440145738329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112112255484748293430492219 168168383227122440145738329)
      ·
        refine ⟨126126287420341830109303747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168168383227122440145738329 126126287420341830109303747)
        ·
          refine ⟨189189431130512745163955621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126126287420341830109303747 189189431130512745163955621)
          ·
            refine ⟨35473018336971139718241679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 189189431130512745163955621 35473018336971139718241679)
            ·
              refine ⟨53209527505456709577362519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35473018336971139718241679 53209527505456709577362519)
              ·
                refine ⟨79814291258185064366043779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53209527505456709577362519 79814291258185064366043779)
                ·
                  refine ⟨119721436887277596549065669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79814291258185064366043779 119721436887277596549065669)
                  ·
                    refine ⟨22447769416364549352949813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 119721436887277596549065669 22447769416364549352949813)
                    ·
                      refine ⟨2104478382784176501839045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22447769416364549352949813 2104478382784176501839045)
                      ·
                        rfl

theorem cell23_4098457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 4, 5].length) (baseStart_4098457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4098457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4098457 prefixEnd_4098457 := by exact prefixLift 4098457
  have htrace : WordTrace (prefixWord ++ tailWord_4098457) baseStart_4098457 baseEnd_4098457 := by
    simpa [prefixWord, tailWord_4098457, baseEnd_4098457] using wordTrace_append hprefix tailTrace_4098457
  have hstable : (prefixWord ++ tailWord_4098457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098457).length < 2 ^ (prefixWord ++ tailWord_4098457).sum := by decide
  have hdescent : baseEnd_4098457 < baseStart_4098457 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098494 : List Nat := [4, 2, 1, 1, 1, 1, 2, 3, 2, 6]
def baseStart_4098494 : Nat := 118140960795 + 4098494 * 2 ^ 59
def prefixEnd_4098494 : Nat := 4983230072969 + 3 ^ 40 * 4098494 * 2
def baseEnd_4098494 : Nat := 701499127189464285692125

theorem tailTrace_4098494 : CollatzResearch.WordTrace tailWord_4098494 prefixEnd_4098494 701499127189464285692125 := by
  unfold tailWord_4098494
  simp only [CollatzResearch.WordTrace]
  refine ⟨18685544601732959986635817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99656237875909119928724357 18685544601732959986635817)
  ·
    refine ⟨14014158451299719989976863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18685544601732959986635817 14014158451299719989976863)
    ·
      refine ⟨21021237676949579984965295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14014158451299719989976863 21021237676949579984965295)
      ·
        refine ⟨31531856515424369977447943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21021237676949579984965295 31531856515424369977447943)
        ·
          refine ⟨47297784773136554966171915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31531856515424369977447943 47297784773136554966171915)
          ·
            refine ⟨70946677159704832449257873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47297784773136554966171915 70946677159704832449257873)
            ·
              refine ⟨53210007869778624336943405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70946677159704832449257873 53210007869778624336943405)
              ·
                refine ⟨19953752951166984126353777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53210007869778624336943405 19953752951166984126353777)
                ·
                  refine ⟨14965314713375238094765333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19953752951166984126353777 14965314713375238094765333)
                  ·
                    refine ⟨701499127189464285692125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14965314713375238094765333 701499127189464285692125)
                    ·
                      rfl

theorem cell23_4098494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_4098494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4098494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4098494 prefixEnd_4098494 := by exact prefixLift 4098494
  have htrace : WordTrace (prefixWord ++ tailWord_4098494) baseStart_4098494 baseEnd_4098494 := by
    simpa [prefixWord, tailWord_4098494, baseEnd_4098494] using wordTrace_append hprefix tailTrace_4098494
  have hstable : (prefixWord ++ tailWord_4098494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098494).length < 2 ^ (prefixWord ++ tailWord_4098494).sum := by decide
  have hdescent : baseEnd_4098494 < baseStart_4098494 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098504 : List Nat := [2, 1, 3, 1, 3, 2, 1, 2, 2, 1, 5]
def baseStart_4098504 : Nat := 118140960795 + 4098504 * 2 ^ 59
def prefixEnd_4098504 : Nat := 4983230072969 + 3 ^ 40 * 4098504 * 2
def baseEnd_4098504 : Nat := 2104502516374937817951329

theorem tailTrace_4098504 : CollatzResearch.WordTrace tailWord_4098504 prefixEnd_4098504 2104502516374937817951329 := by
  unfold tailWord_4098504
  simp only [CollatzResearch.WordTrace]
  refine ⟨74742360771913725800475283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99656481029218301067300377 74742360771913725800475283)
  ·
    refine ⟨112113541157870588700712925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74742360771913725800475283 112113541157870588700712925)
    ·
      refine ⟨42042577934201470762767347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112113541157870588700712925 42042577934201470762767347)
      ·
        refine ⟨63063866901302206144151021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42042577934201470762767347 63063866901302206144151021)
        ·
          refine ⟨23648950087988327304056633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63063866901302206144151021 23648950087988327304056633)
          ·
            refine ⟨17736712565991245478042475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23648950087988327304056633 17736712565991245478042475)
            ·
              refine ⟨26605068848986868217063713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17736712565991245478042475 26605068848986868217063713)
              ·
                refine ⟨19953801636740151162797785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26605068848986868217063713 19953801636740151162797785)
                ·
                  refine ⟨14965351227555113372098339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19953801636740151162797785 14965351227555113372098339)
                  ·
                    refine ⟨22448026841332670058147509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14965351227555113372098339 22448026841332670058147509)
                    ·
                      refine ⟨2104502516374937817951329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22448026841332670058147509 2104502516374937817951329)
                      ·
                        rfl

theorem cell23_4098504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 2, 1, 5].length) (baseStart_4098504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4098504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4098504 prefixEnd_4098504 := by exact prefixLift 4098504
  have htrace : WordTrace (prefixWord ++ tailWord_4098504) baseStart_4098504 baseEnd_4098504 := by
    simpa [prefixWord, tailWord_4098504, baseEnd_4098504] using wordTrace_append hprefix tailTrace_4098504
  have hstable : (prefixWord ++ tailWord_4098504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098504).length < 2 ^ (prefixWord ++ tailWord_4098504).sum := by decide
  have hdescent : baseEnd_4098504 < baseStart_4098504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098507 : List Nat := [1, 1, 1, 1, 3, 3, 1, 3, 9]
def baseStart_4098507 : Nat := 118140960795 + 4098507 * 2 ^ 59
def prefixEnd_4098507 : Nat := 4983230072969 + 3 ^ 40 * 4098507 * 2
def baseEnd_4098507 : Nat := 233833784090766811801535

theorem tailTrace_4098507 : CollatzResearch.WordTrace tailWord_4098507 prefixEnd_4098507 233833784090766811801535 := by
  unfold tailWord_4098507
  simp only [CollatzResearch.WordTrace]
  refine ⟨149484830962816583113309775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99656553975211055408873183 149484830962816583113309775)
  ·
    refine ⟨224227246444224874669964663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149484830962816583113309775 224227246444224874669964663)
    ·
      refine ⟨336340869666337312004946995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224227246444224874669964663 336340869666337312004946995)
      ·
        refine ⟨504511304499505968007420493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336340869666337312004946995 504511304499505968007420493)
        ·
          refine ⟨189191739187314738002782685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 504511304499505968007420493 189191739187314738002782685)
          ·
            refine ⟨70946902195243026751043507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189191739187314738002782685 70946902195243026751043507)
            ·
              refine ⟨106420353292864540126565261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70946902195243026751043507 106420353292864540126565261)
              ·
                refine ⟨39907632484824202547461973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106420353292864540126565261 39907632484824202547461973)
                ·
                  refine ⟨233833784090766811801535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 39907632484824202547461973 233833784090766811801535)
                  ·
                    rfl

theorem cell23_4098507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 9].length) (baseStart_4098507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4098507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4098507 prefixEnd_4098507 := by exact prefixLift 4098507
  have htrace : WordTrace (prefixWord ++ tailWord_4098507) baseStart_4098507 baseEnd_4098507 := by
    simpa [prefixWord, tailWord_4098507, baseEnd_4098507] using wordTrace_append hprefix tailTrace_4098507
  have hstable : (prefixWord ++ tailWord_4098507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098507).length < 2 ^ (prefixWord ++ tailWord_4098507).sum := by decide
  have hdescent : baseEnd_4098507 < baseStart_4098507 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098535 : List Nat := [1, 1, 5, 2, 1, 1, 4, 2, 2, 2, 2]
def baseStart_4098535 : Nat := 118140960795 + 4098535 * 2 ^ 59
def prefixEnd_4098535 : Nat := 4983230072969 + 3 ^ 40 * 4098535 * 2
def baseEnd_4098535 : Nat := 2104518434275227196663687

theorem tailTrace_4098535 : CollatzResearch.WordTrace tailWord_4098535 prefixEnd_4098535 2104518434275227196663687 := by
  unfold tailWord_4098535
  simp only [CollatzResearch.WordTrace]
  refine ⟨149485852206715143895329059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99657234804476762596886039 149485852206715143895329059)
  ·
    refine ⟨224228778310072715842993589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149485852206715143895329059 224228778310072715842993589)
    ·
      refine ⟨21021447966569317110280649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 224228778310072715842993589 21021447966569317110280649)
      ·
        refine ⟨15766085974926987832710487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21021447966569317110280649 15766085974926987832710487)
        ·
          refine ⟨23649128962390481749065731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15766085974926987832710487 23649128962390481749065731)
          ·
            refine ⟨35473693443585722623598597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23649128962390481749065731 35473693443585722623598597)
            ·
              refine ⟨6651317520672322991924737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35473693443585722623598597 6651317520672322991924737)
              ·
                refine ⟨4988488140504242243943553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6651317520672322991924737 4988488140504242243943553)
                ·
                  refine ⟨3741366105378181682957665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4988488140504242243943553 3741366105378181682957665)
                  ·
                    refine ⟨2806024579033636262218249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3741366105378181682957665 2806024579033636262218249)
                    ·
                      refine ⟨2104518434275227196663687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2806024579033636262218249 2104518434275227196663687)
                      ·
                        rfl

theorem cell23_4098535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 2, 2, 2, 2].length) (baseStart_4098535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4098535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4098535 prefixEnd_4098535 := by exact prefixLift 4098535
  have htrace : WordTrace (prefixWord ++ tailWord_4098535) baseStart_4098535 baseEnd_4098535 := by
    simpa [prefixWord, tailWord_4098535, baseEnd_4098535] using wordTrace_append hprefix tailTrace_4098535
  have hstable : (prefixWord ++ tailWord_4098535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098535).length < 2 ^ (prefixWord ++ tailWord_4098535).sum := by decide
  have hdescent : baseEnd_4098535 < baseStart_4098535 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098571 : List Nat := [1, 1, 1, 1, 7, 1, 3, 1, 2, 5]
def baseStart_4098571 : Nat := 118140960795 + 4098571 * 2 ^ 59
def prefixEnd_4098571 : Nat := 4983230072969 + 3 ^ 40 * 4098571 * 2
def baseEnd_4098571 : Nat := 701512306526263018604507

theorem tailTrace_4098571 : CollatzResearch.WordTrace tailWord_4098571 prefixEnd_4098571 701512306526263018604507 := by
  unfold tailWord_4098571
  simp only [CollatzResearch.WordTrace]
  refine ⟨149487165234584722043639567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99658110156389814695759711 149487165234584722043639567)
  ·
    refine ⟨224230747851877083065459351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149487165234584722043639567 224230747851877083065459351)
    ·
      refine ⟨336346121777815624598189027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224230747851877083065459351 336346121777815624598189027)
      ·
        refine ⟨504519182666723436897283541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336346121777815624598189027 504519182666723436897283541)
        ·
          refine ⟨11824668343751330552280083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 504519182666723436897283541 11824668343751330552280083)
          ·
            refine ⟨17737002515626995828420125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11824668343751330552280083 17737002515626995828420125)
            ·
              refine ⟨6651375943360123435657547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17737002515626995828420125 6651375943360123435657547)
              ·
                refine ⟨9977063915040185153486321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6651375943360123435657547 9977063915040185153486321)
                ·
                  refine ⟨7482797936280138865114741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9977063915040185153486321 7482797936280138865114741)
                  ·
                    refine ⟨701512306526263018604507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7482797936280138865114741 701512306526263018604507)
                    ·
                      rfl

theorem cell23_4098571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 1, 2, 5].length) (baseStart_4098571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4098571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4098571 prefixEnd_4098571 := by exact prefixLift 4098571
  have htrace : WordTrace (prefixWord ++ tailWord_4098571) baseStart_4098571 baseEnd_4098571 := by
    simpa [prefixWord, tailWord_4098571, baseEnd_4098571] using wordTrace_append hprefix tailTrace_4098571
  have hstable : (prefixWord ++ tailWord_4098571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098571).length < 2 ^ (prefixWord ++ tailWord_4098571).sum := by decide
  have hdescent : baseEnd_4098571 < baseStart_4098571 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098652 : List Nat := [2, 2, 4, 1, 4, 1, 1, 1, 3, 4]
def baseStart_4098652 : Nat := 118140960795 + 4098652 * 2 ^ 59
def prefixEnd_4098652 : Nat := 4983230072969 + 3 ^ 40 * 4098652 * 2
def baseEnd_4098652 : Nat := 701526170503934412966883

theorem tailTrace_4098652 : CollatzResearch.WordTrace tailWord_4098652 prefixEnd_4098652 701526170503934412966883 := by
  unfold tailWord_4098652
  simp only [CollatzResearch.WordTrace]
  refine ⟨74745059773645636438669105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99660079698194181918225473 74745059773645636438669105)
  ·
    refine ⟨56058794830234227329001829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74745059773645636438669105 56058794830234227329001829)
    ·
      refine ⟨10511024030668917624187843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56058794830234227329001829 10511024030668917624187843)
      ·
        refine ⟨15766536046003376436281765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10511024030668917624187843 15766536046003376436281765)
        ·
          refine ⟨2956225508625633081802831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15766536046003376436281765 2956225508625633081802831)
          ·
            refine ⟨4434338262938449622704247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2956225508625633081802831 4434338262938449622704247)
            ·
              refine ⟨6651507394407674434056371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4434338262938449622704247 6651507394407674434056371)
              ·
                refine ⟨9977261091611511651084557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6651507394407674434056371 9977261091611511651084557)
                ·
                  refine ⟨3741472909354316869156709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9977261091611511651084557 3741472909354316869156709)
                  ·
                    refine ⟨701526170503934412966883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3741472909354316869156709 701526170503934412966883)
                    ·
                      rfl

theorem cell23_4098652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_4098652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4098652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4098652 prefixEnd_4098652 := by exact prefixLift 4098652
  have htrace : WordTrace (prefixWord ++ tailWord_4098652) baseStart_4098652 baseEnd_4098652 := by
    simpa [prefixWord, tailWord_4098652, baseEnd_4098652] using wordTrace_append hprefix tailTrace_4098652
  have hstable : (prefixWord ++ tailWord_4098652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098652).length < 2 ^ (prefixWord ++ tailWord_4098652).sum := by decide
  have hdescent : baseEnd_4098652 < baseStart_4098652 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098691 : List Nat := [1, 1, 1, 3, 3, 1, 2, 1, 6, 4]
def baseStart_4098691 : Nat := 118140960795 + 4098691 * 2 ^ 59
def prefixEnd_4098691 : Nat := 4983230072969 + 3 ^ 40 * 4098691 * 2
def baseEnd_4098691 : Nat := 701532845752442862104323

theorem tailTrace_4098691 : CollatzResearch.WordTrace tailWord_4098691 prefixEnd_4098691 701532845752442862104323 := by
  unfold tailWord_4098691
  simp only [CollatzResearch.WordTrace]
  refine ⟨149491541994149982538007927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99661027996099988358671951 149491541994149982538007927)
  ·
    refine ⟨224237312991224973807011891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149491541994149982538007927 224237312991224973807011891)
    ·
      refine ⟨336355969486837460710517837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224237312991224973807011891 336355969486837460710517837)
      ·
        refine ⟨126133488557564047766444189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 336355969486837460710517837 126133488557564047766444189)
        ·
          refine ⟨47300058209086517912416571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126133488557564047766444189 47300058209086517912416571)
          ·
            refine ⟨70950087313629776868624857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47300058209086517912416571 70950087313629776868624857)
            ·
              refine ⟨53212565485222332651468643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70950087313629776868624857 53212565485222332651468643)
              ·
                refine ⟨79818848227833498977202965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53212565485222332651468643 79818848227833498977202965)
                ·
                  refine ⟨3741508510679695264556389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 79818848227833498977202965 3741508510679695264556389)
                  ·
                    refine ⟨701532845752442862104323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3741508510679695264556389 701532845752442862104323)
                    ·
                      rfl

theorem cell23_4098691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 6, 4].length) (baseStart_4098691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4098691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4098691 prefixEnd_4098691 := by exact prefixLift 4098691
  have htrace : WordTrace (prefixWord ++ tailWord_4098691) baseStart_4098691 baseEnd_4098691 := by
    simpa [prefixWord, tailWord_4098691, baseEnd_4098691] using wordTrace_append hprefix tailTrace_4098691
  have hstable : (prefixWord ++ tailWord_4098691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098691).length < 2 ^ (prefixWord ++ tailWord_4098691).sum := by decide
  have hdescent : baseEnd_4098691 < baseStart_4098691 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098711 : List Nat := [1, 1, 3, 3, 2, 1, 1, 2, 3, 2, 4]
def baseStart_4098711 : Nat := 118140960795 + 4098711 * 2 ^ 59
def prefixEnd_4098711 : Nat := 4983230072969 + 3 ^ 40 * 4098711 * 2
def baseEnd_4098711 : Nat := 2104608806870418508062877

theorem tailTrace_4098711 : CollatzResearch.WordTrace tailWord_4098711 prefixEnd_4098711 2104608806870418508062877 := by
  unfold tailWord_4098711
  simp only [CollatzResearch.WordTrace]
  refine ⟨149492271454077525953735987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99661514302718350635823991 149492271454077525953735987)
  ·
    refine ⟨224238407181116288930603981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149492271454077525953735987 224238407181116288930603981)
    ·
      refine ⟨84089402692918608348976493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224238407181116288930603981 84089402692918608348976493)
      ·
        refine ⟨31533526009844478130866185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84089402692918608348976493 31533526009844478130866185)
        ·
          refine ⟨23650144507383358598149639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31533526009844478130866185 23650144507383358598149639)
          ·
            refine ⟨35475216761075037897224459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23650144507383358598149639 35475216761075037897224459)
            ·
              refine ⟨53212825141612556845836689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35475216761075037897224459 53212825141612556845836689)
              ·
                refine ⟨39909618856209417634377517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53212825141612556845836689 39909618856209417634377517)
                ·
                  refine ⟨14966107071078531612891569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39909618856209417634377517 14966107071078531612891569)
                  ·
                    refine ⟨11224580303308898709668677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14966107071078531612891569 11224580303308898709668677)
                    ·
                      refine ⟨2104608806870418508062877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11224580303308898709668677 2104608806870418508062877)
                      ·
                        rfl

theorem cell23_4098711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_4098711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4098711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4098711 prefixEnd_4098711 := by exact prefixLift 4098711
  have htrace : WordTrace (prefixWord ++ tailWord_4098711) baseStart_4098711 baseEnd_4098711 := by
    simpa [prefixWord, tailWord_4098711, baseEnd_4098711] using wordTrace_append hprefix tailTrace_4098711
  have hstable : (prefixWord ++ tailWord_4098711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098711).length < 2 ^ (prefixWord ++ tailWord_4098711).sum := by decide
  have hdescent : baseEnd_4098711 < baseStart_4098711 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098718 : List Nat := [4, 3, 1, 1, 1, 1, 2, 1, 3, 1, 5]
def baseStart_4098718 : Nat := 118140960795 + 4098718 * 2 ^ 59
def prefixEnd_4098718 : Nat := 4983230072969 + 3 ^ 40 * 4098718 * 2
def baseEnd_4098718 : Nat := 2104612401234999980675345

theorem tailTrace_4098718 : CollatzResearch.WordTrace tailWord_4098718 prefixEnd_4098718 2104612401234999980675345 := by
  unfold tailWord_4098718
  simp only [CollatzResearch.WordTrace]
  refine ⟨18686565845631520768655101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99661684510034777432827205 18686565845631520768655101)
  ·
    refine ⟨7007462192111820288245663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18686565845631520768655101 7007462192111820288245663)
    ·
      refine ⟨10511193288167730432368495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7007462192111820288245663 10511193288167730432368495)
      ·
        refine ⟨15766789932251595648552743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10511193288167730432368495 15766789932251595648552743)
        ·
          refine ⟨23650184898377393472829115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15766789932251595648552743 23650184898377393472829115)
          ·
            refine ⟨35475277347566090209243673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23650184898377393472829115 35475277347566090209243673)
            ·
              refine ⟨26606458010674567656932755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35475277347566090209243673 26606458010674567656932755)
              ·
                refine ⟨39909687016011851485399133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26606458010674567656932755 39909687016011851485399133)
                ·
                  refine ⟨14966132631004444307024675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39909687016011851485399133 14966132631004444307024675)
                  ·
                    refine ⟨22449198946506666460537013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14966132631004444307024675 22449198946506666460537013)
                    ·
                      refine ⟨2104612401234999980675345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22449198946506666460537013 2104612401234999980675345)
                      ·
                        rfl

theorem cell23_4098718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_4098718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4098718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4098718 prefixEnd_4098718 := by exact prefixLift 4098718
  have htrace : WordTrace (prefixWord ++ tailWord_4098718) baseStart_4098718 baseEnd_4098718 := by
    simpa [prefixWord, tailWord_4098718, baseEnd_4098718] using wordTrace_append hprefix tailTrace_4098718
  have hstable : (prefixWord ++ tailWord_4098718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098718).length < 2 ^ (prefixWord ++ tailWord_4098718).sum := by decide
  have hdescent : baseEnd_4098718 < baseStart_4098718 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098748 : List Nat := [2, 2, 2, 3, 1, 1, 1, 4, 1, 3, 3]
def baseStart_4098748 : Nat := 118140960795 + 4098748 * 2 ^ 59
def prefixEnd_4098748 : Nat := 4983230072969 + 3 ^ 40 * 4098748 * 2
def baseEnd_4098748 : Nat := 2104627805654634863300207

theorem tailTrace_4098748 : CollatzResearch.WordTrace tailWord_4098748 prefixEnd_4098748 2104627805654634863300207 := by
  unfold tailWord_4098748
  simp only [CollatzResearch.WordTrace]
  refine ⟨74746810477471740636416449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99662413969962320848555265 74746810477471740636416449)
  ·
    refine ⟨56060107858103805477312337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74746810477471740636416449 56060107858103805477312337)
    ·
      refine ⟨42045080893577854107984253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56060107858103805477312337 42045080893577854107984253)
      ·
        refine ⟨15766905335091695290494095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42045080893577854107984253 15766905335091695290494095)
        ·
          refine ⟨23650358002637542935741143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15766905335091695290494095 23650358002637542935741143)
          ·
            refine ⟨35475537003956314403611715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23650358002637542935741143 35475537003956314403611715)
            ·
              refine ⟨53213305505934471605417573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35475537003956314403611715 53213305505934471605417573)
              ·
                refine ⟨9977494782362713426015795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53213305505934471605417573 9977494782362713426015795)
                ·
                  refine ⟨14966242173544070139023693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9977494782362713426015795 14966242173544070139023693)
                  ·
                    refine ⟨5612340815079026302133885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14966242173544070139023693 5612340815079026302133885)
                    ·
                      refine ⟨2104627805654634863300207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5612340815079026302133885 2104627805654634863300207)
                      ·
                        rfl

theorem cell23_4098748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_4098748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4098748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4098748 prefixEnd_4098748 := by exact prefixLift 4098748
  have htrace : WordTrace (prefixWord ++ tailWord_4098748) baseStart_4098748 baseEnd_4098748 := by
    simpa [prefixWord, tailWord_4098748, baseEnd_4098748] using wordTrace_append hprefix tailTrace_4098748
  have hstable : (prefixWord ++ tailWord_4098748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098748).length < 2 ^ (prefixWord ++ tailWord_4098748).sum := by decide
  have hdescent : baseEnd_4098748 < baseStart_4098748 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098749 : List Nat := [1, 4, 1, 2, 1, 4, 2, 3, 1, 2, 2]
def baseStart_4098749 : Nat := 118140960795 + 4098749 * 2 ^ 59
def prefixEnd_4098749 : Nat := 4983230072969 + 3 ^ 40 * 4098749 * 2
def baseEnd_4098749 : Nat := 2104628319135289359387703

theorem tailTrace_4098749 : CollatzResearch.WordTrace tailWord_4098749 prefixEnd_4098749 2104628319135289359387703 := by
  unfold tailWord_4098749
  simp only [CollatzResearch.WordTrace]
  refine ⟨149493657427939858443619301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99662438285293238962412867 149493657427939858443619301)
  ·
    refine ⟨28030060767738723458178619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149493657427939858443619301 28030060767738723458178619)
    ·
      refine ⟨42045091151608085187267929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28030060767738723458178619 42045091151608085187267929)
      ·
        refine ⟨31533818363706063890450947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42045091151608085187267929 31533818363706063890450947)
        ·
          refine ⟨47300727545559095835676421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31533818363706063890450947 47300727545559095835676421)
          ·
            refine ⟨8868886414792330469189329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47300727545559095835676421 8868886414792330469189329)
            ·
              refine ⟨6651664811094247851891997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8868886414792330469189329 6651664811094247851891997)
              ·
                refine ⟨2494374304160342944459499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6651664811094247851891997 2494374304160342944459499)
                ·
                  refine ⟨3741561456240514416689249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2494374304160342944459499 3741561456240514416689249)
                  ·
                    refine ⟨2806171092180385812516937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3741561456240514416689249 2806171092180385812516937)
                    ·
                      refine ⟨2104628319135289359387703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2806171092180385812516937 2104628319135289359387703)
                      ·
                        rfl

theorem cell23_4098749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 3, 1, 2, 2].length) (baseStart_4098749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4098749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4098749 prefixEnd_4098749 := by exact prefixLift 4098749
  have htrace : WordTrace (prefixWord ++ tailWord_4098749) baseStart_4098749 baseEnd_4098749 := by
    simpa [prefixWord, tailWord_4098749, baseEnd_4098749] using wordTrace_append hprefix tailTrace_4098749
  have hstable : (prefixWord ++ tailWord_4098749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098749).length < 2 ^ (prefixWord ++ tailWord_4098749).sum := by decide
  have hdescent : baseEnd_4098749 < baseStart_4098749 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098752 : List Nat := [2, 1, 1, 2, 4, 4, 2, 1, 1, 2, 3]
def baseStart_4098752 : Nat := 118140960795 + 4098752 * 2 ^ 59
def prefixEnd_4098752 : Nat := 4983230072969 + 3 ^ 40 * 4098752 * 2
def baseEnd_4098752 : Nat := 2104629859577252847650189

theorem tailTrace_4098752 : CollatzResearch.WordTrace tailWord_4098752 prefixEnd_4098752 2104629859577252847650189 := by
  unfold tailWord_4098752
  simp only [CollatzResearch.WordTrace]
  refine ⟨74746883423464494977989255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99662511231285993303985673 74746883423464494977989255)
  ·
    refine ⟨112120325135196742466983883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74746883423464494977989255 112120325135196742466983883)
    ·
      refine ⟨168180487702795113700475825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112120325135196742466983883 168180487702795113700475825)
      ·
        refine ⟨126135365777096335275356869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168180487702795113700475825 126135365777096335275356869)
        ·
          refine ⟨23650381083205562864129413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126135365777096335275356869 23650381083205562864129413)
          ·
            refine ⟨4434446453101043037024265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23650381083205562864129413 4434446453101043037024265)
            ·
              refine ⟨3325834839825782277768199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4434446453101043037024265 3325834839825782277768199)
              ·
                refine ⟨4988752259738673416652299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3325834839825782277768199 4988752259738673416652299)
                ·
                  refine ⟨7483128389608010124978449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4988752259738673416652299 7483128389608010124978449)
                  ·
                    refine ⟨5612346292206007593733837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7483128389608010124978449 5612346292206007593733837)
                    ·
                      refine ⟨2104629859577252847650189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5612346292206007593733837 2104629859577252847650189)
                      ·
                        rfl

theorem cell23_4098752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 2, 1, 1, 2, 3].length) (baseStart_4098752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4098752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4098752 prefixEnd_4098752 := by exact prefixLift 4098752
  have htrace : WordTrace (prefixWord ++ tailWord_4098752) baseStart_4098752 baseEnd_4098752 := by
    simpa [prefixWord, tailWord_4098752, baseEnd_4098752] using wordTrace_append hprefix tailTrace_4098752
  have hstable : (prefixWord ++ tailWord_4098752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098752).length < 2 ^ (prefixWord ++ tailWord_4098752).sum := by decide
  have hdescent : baseEnd_4098752 < baseStart_4098752 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098839 : List Nat := [1, 1, 3, 4, 3, 1, 1, 3, 2, 2, 2]
def baseStart_4098839 : Nat := 118140960795 + 4098839 * 2 ^ 59
def prefixEnd_4098839 : Nat := 4983230072969 + 3 ^ 40 * 4098839 * 2
def baseEnd_4098839 : Nat := 2104674532394194007262289

theorem tailTrace_4098839 : CollatzResearch.WordTrace tailWord_4098839 prefixEnd_4098839 2104674532394194007262289 := by
  unfold tailWord_4098839
  simp only [CollatzResearch.WordTrace]
  refine ⟨149496939997613803814395571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99664626665075869209597047 149496939997613803814395571)
  ·
    refine ⟨224245409996420705721593357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149496939997613803814395571 224245409996420705721593357)
    ·
      refine ⟨84092028748657764645597509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224245409996420705721593357 84092028748657764645597509)
      ·
        refine ⟨15767255390373330871049533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84092028748657764645597509 15767255390373330871049533)
        ·
          refine ⟨5912720771389999076643575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15767255390373330871049533 5912720771389999076643575)
          ·
            refine ⟨8869081157084998614965363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5912720771389999076643575 8869081157084998614965363)
            ·
              refine ⟨13303621735627497922448045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8869081157084998614965363 13303621735627497922448045)
              ·
                refine ⟨4988858150860311720918017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13303621735627497922448045 4988858150860311720918017)
                ·
                  refine ⟨3741643613145233790688513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4988858150860311720918017 3741643613145233790688513)
                  ·
                    refine ⟨2806232709858925343016385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3741643613145233790688513 2806232709858925343016385)
                    ·
                      refine ⟨2104674532394194007262289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2806232709858925343016385 2104674532394194007262289)
                      ·
                        rfl

theorem cell23_4098839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 3, 2, 2, 2].length) (baseStart_4098839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4098839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4098839 prefixEnd_4098839 := by exact prefixLift 4098839
  have htrace : WordTrace (prefixWord ++ tailWord_4098839) baseStart_4098839 baseEnd_4098839 := by
    simpa [prefixWord, tailWord_4098839, baseEnd_4098839] using wordTrace_append hprefix tailTrace_4098839
  have hstable : (prefixWord ++ tailWord_4098839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098839).length < 2 ^ (prefixWord ++ tailWord_4098839).sum := by decide
  have hdescent : baseEnd_4098839 < baseStart_4098839 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098841 : List Nat := [1, 2, 1, 2, 1, 1, 1, 6, 1, 7]
def baseStart_4098841 : Nat := 118140960795 + 4098841 * 2 ^ 59
def prefixEnd_4098841 : Nat := 4983230072969 + 3 ^ 40 * 4098841 * 2
def baseEnd_4098841 : Nat := 701558519785167666479093

theorem tailTrace_4098841 : CollatzResearch.WordTrace tailWord_4098841 prefixEnd_4098841 701558519785167666479093 := by
  unfold tailWord_4098841
  simp only [CollatzResearch.WordTrace]
  refine ⟨149497012943606558155968377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99664675295737705437312251 149497012943606558155968377)
  ·
    refine ⟨112122759707704918616976283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149497012943606558155968377 112122759707704918616976283)
    ·
      refine ⟨168184139561557377925464425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112122759707704918616976283 168184139561557377925464425)
      ·
        refine ⟨126138104671168033444098319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168184139561557377925464425 126138104671168033444098319)
        ·
          refine ⟨189207157006752050166147479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126138104671168033444098319 189207157006752050166147479)
          ·
            refine ⟨283810735510128075249221219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189207157006752050166147479 283810735510128075249221219)
            ·
              refine ⟨425716103265192112873831829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283810735510128075249221219 425716103265192112873831829)
              ·
                refine ⟨19955442340555880290960867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 425716103265192112873831829 19955442340555880290960867)
                ·
                  refine ⟨29933163510833820436441301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19955442340555880290960867 29933163510833820436441301)
                  ·
                    refine ⟨701558519785167666479093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29933163510833820436441301 701558519785167666479093)
                    ·
                      rfl

theorem cell23_4098841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 7].length) (baseStart_4098841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4098841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4098841 prefixEnd_4098841 := by exact prefixLift 4098841
  have htrace : WordTrace (prefixWord ++ tailWord_4098841) baseStart_4098841 baseEnd_4098841 := by
    simpa [prefixWord, tailWord_4098841, baseEnd_4098841] using wordTrace_append hprefix tailTrace_4098841
  have hstable : (prefixWord ++ tailWord_4098841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098841).length < 2 ^ (prefixWord ++ tailWord_4098841).sum := by decide
  have hdescent : baseEnd_4098841 < baseStart_4098841 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098851 : List Nat := [1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 7]
def baseStart_4098851 : Nat := 118140960795 + 4098851 * 2 ^ 59
def prefixEnd_4098851 : Nat := 4983230072969 + 3 ^ 40 * 4098851 * 2
def baseEnd_4098851 : Nat := 2104680694162047960312233

theorem tailTrace_4098851 : CollatzResearch.WordTrace tailWord_4098851 prefixEnd_4098851 2104680694162047960312233 := by
  unfold tailWord_4098851
  simp only [CollatzResearch.WordTrace]
  refine ⟨149497377673570329863832407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99664918449046886575888271 149497377673570329863832407)
  ·
    refine ⟨224246066510355494795748611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149497377673570329863832407 224246066510355494795748611)
    ·
      refine ⟨336369099765533242193622917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224246066510355494795748611 336369099765533242193622917)
      ·
        refine ⟨63069206206037482911304297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 336369099765533242193622917 63069206206037482911304297)
        ·
          refine ⟨47301904654528112183478223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63069206206037482911304297 47301904654528112183478223)
          ·
            refine ⟨70952856981792168275217335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47301904654528112183478223 70952856981792168275217335)
            ·
              refine ⟨106429285472688252412826003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70952856981792168275217335 106429285472688252412826003)
              ·
                refine ⟨159643928209032378619239005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106429285472688252412826003 159643928209032378619239005)
                ·
                  refine ⟨59866473078387141982214627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 159643928209032378619239005 59866473078387141982214627)
                  ·
                    refine ⟨89799709617580712973321941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59866473078387141982214627 89799709617580712973321941)
                    ·
                      refine ⟨2104680694162047960312233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 89799709617580712973321941 2104680694162047960312233)
                      ·
                        rfl

theorem cell23_4098851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_4098851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4098851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4098851 prefixEnd_4098851 := by exact prefixLift 4098851
  have htrace : WordTrace (prefixWord ++ tailWord_4098851) baseStart_4098851 baseEnd_4098851 := by
    simpa [prefixWord, tailWord_4098851, baseEnd_4098851] using wordTrace_append hprefix tailTrace_4098851
  have hstable : (prefixWord ++ tailWord_4098851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098851).length < 2 ^ (prefixWord ++ tailWord_4098851).sum := by decide
  have hdescent : baseEnd_4098851 < baseStart_4098851 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098905 : List Nat := [1, 2, 1, 2, 2, 5, 1, 2, 3, 4]
def baseStart_4098905 : Nat := 118140960795 + 4098905 * 2 ^ 59
def prefixEnd_4098905 : Nat := 4983230072969 + 3 ^ 40 * 4098905 * 2
def baseEnd_4098905 : Nat := 701569474039130249678995

theorem tailTrace_4098905 : CollatzResearch.WordTrace tailWord_4098905 prefixEnd_4098905 701569474039130249678995 := by
  unfold tailWord_4098905
  simp only [CollatzResearch.WordTrace]
  refine ⟨149499347215374697086298169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99666231476916464724198779 149499347215374697086298169)
  ·
    refine ⟨112124510411531022814723627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149499347215374697086298169 112124510411531022814723627)
    ·
      refine ⟨168186765617296534222085441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112124510411531022814723627 168186765617296534222085441)
      ·
        refine ⟨126140074212972400666564081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168186765617296534222085441 126140074212972400666564081)
        ·
          refine ⟨94605055659729300499923061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126140074212972400666564081 94605055659729300499923061)
          ·
            refine ⟨8869223968099621921867787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94605055659729300499923061 8869223968099621921867787)
            ·
              refine ⟨13303835952149432882801681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8869223968099621921867787 13303835952149432882801681)
              ·
                refine ⟨9977876964112074662101261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13303835952149432882801681 9977876964112074662101261)
                ·
                  refine ⟨3741703861542027998287973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9977876964112074662101261 3741703861542027998287973)
                  ·
                    refine ⟨701569474039130249678995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3741703861542027998287973 701569474039130249678995)
                    ·
                      rfl

theorem cell23_4098905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 2, 3, 4].length) (baseStart_4098905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4098905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4098905 prefixEnd_4098905 := by exact prefixLift 4098905
  have htrace : WordTrace (prefixWord ++ tailWord_4098905) baseStart_4098905 baseEnd_4098905 := by
    simpa [prefixWord, tailWord_4098905, baseEnd_4098905] using wordTrace_append hprefix tailTrace_4098905
  have hstable : (prefixWord ++ tailWord_4098905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098905).length < 2 ^ (prefixWord ++ tailWord_4098905).sum := by decide
  have hdescent : baseEnd_4098905 < baseStart_4098905 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098915 : List Nat := [1, 1, 1, 5, 3, 2, 1, 1, 1, 4, 3]
def baseStart_4098915 : Nat := 118140960795 + 4098915 * 2 ^ 59
def prefixEnd_4098915 : Nat := 4983230072969 + 3 ^ 40 * 4098915 * 2
def baseEnd_4098915 : Nat := 2104713556923935709911939

theorem tailTrace_4098915 : CollatzResearch.WordTrace tailWord_4098915 prefixEnd_4098915 2104713556923935709911939 := by
  unfold tailWord_4098915
  simp only [CollatzResearch.WordTrace]
  refine ⟨149499711945338468794162199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99666474630225645862774799 149499711945338468794162199)
  ·
    refine ⟨224249567918007703191243299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149499711945338468794162199 224249567918007703191243299)
    ·
      refine ⟨336374351877011554786864949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224249567918007703191243299 336374351877011554786864949)
      ·
        refine ⟨31535095488469833261268589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 336374351877011554786864949 31535095488469833261268589)
        ·
          refine ⟨11825660808176187472975721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31535095488469833261268589 11825660808176187472975721)
          ·
            refine ⟨8869245606132140604731791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11825660808176187472975721 8869245606132140604731791)
            ·
              refine ⟨13303868409198210907097687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8869245606132140604731791 13303868409198210907097687)
              ·
                refine ⟨19955802613797316360646531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13303868409198210907097687 19955802613797316360646531)
                ·
                  refine ⟨29933703920695974540969797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19955802613797316360646531 29933703920695974540969797)
                  ·
                    refine ⟨5612569485130495226431837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29933703920695974540969797 5612569485130495226431837)
                    ·
                      refine ⟨2104713556923935709911939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5612569485130495226431837 2104713556923935709911939)
                      ·
                        rfl

theorem cell23_4098915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 4, 3].length) (baseStart_4098915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4098915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4098915 prefixEnd_4098915 := by exact prefixLift 4098915
  have htrace : WordTrace (prefixWord ++ tailWord_4098915) baseStart_4098915 baseEnd_4098915 := by
    simpa [prefixWord, tailWord_4098915, baseEnd_4098915] using wordTrace_append hprefix tailTrace_4098915
  have hstable : (prefixWord ++ tailWord_4098915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098915).length < 2 ^ (prefixWord ++ tailWord_4098915).sum := by decide
  have hdescent : baseEnd_4098915 < baseStart_4098915 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098952 : List Nat := [2, 1, 3, 3, 2, 2, 3, 1, 6]
def baseStart_4098952 : Nat := 118140960795 + 4098952 * 2 ^ 59
def prefixEnd_4098952 : Nat := 4983230072969 + 3 ^ 40 * 4098952 * 2
def baseEnd_4098952 : Nat := 233859172856461340572141

theorem tailTrace_4098952 : CollatzResearch.WordTrace tailWord_4098952 prefixEnd_4098952 233859172856461340572141 := by
  unfold tailWord_4098952
  simp only [CollatzResearch.WordTrace]
  refine ⟨74750530723102212056629555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99667374297469616075506073 74750530723102212056629555)
  ·
    refine ⟨112125796084653318084944333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74750530723102212056629555 112125796084653318084944333)
    ·
      refine ⟨42047173531744994281854125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112125796084653318084944333 42047173531744994281854125)
      ·
        refine ⟨15767690074404372855695297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42047173531744994281854125 15767690074404372855695297)
        ·
          refine ⟨11825767555803279641771473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15767690074404372855695297 11825767555803279641771473)
          ·
            refine ⟨8869325666852459731328605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11825767555803279641771473 8869325666852459731328605)
            ·
              refine ⟨3325997125069672399248227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8869325666852459731328605 3325997125069672399248227)
              ·
                refine ⟨4988995687604508598872341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3325997125069672399248227 4988995687604508598872341)
                ·
                  refine ⟨233859172856461340572141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4988995687604508598872341 233859172856461340572141)
                  ·
                    rfl

theorem cell23_4098952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 3, 1, 6].length) (baseStart_4098952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4098952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4098952 prefixEnd_4098952 := by exact prefixLift 4098952
  have htrace : WordTrace (prefixWord ++ tailWord_4098952) baseStart_4098952 baseEnd_4098952 := by
    simpa [prefixWord, tailWord_4098952, baseEnd_4098952] using wordTrace_append hprefix tailTrace_4098952
  have hstable : (prefixWord ++ tailWord_4098952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098952).length < 2 ^ (prefixWord ++ tailWord_4098952).sum := by decide
  have hdescent : baseEnd_4098952 < baseStart_4098952 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098955 : List Nat := [1, 1, 1, 1, 4, 2, 3, 2, 1, 5, 2]
def baseStart_4098955 : Nat := 118140960795 + 4098955 * 2 ^ 59
def prefixEnd_4098955 : Nat := 4983230072969 + 3 ^ 40 * 4098955 * 2
def baseEnd_4098955 : Nat := 2104734096150115553411755

theorem tailTrace_4098955 : CollatzResearch.WordTrace tailWord_4098955 prefixEnd_4098955 2104734096150115553411755 := by
  unfold tailWord_4098955
  simp only [CollatzResearch.WordTrace]
  refine ⟨149501170865193555625618319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99667447243462370417078879 149501170865193555625618319)
  ·
    refine ⟨224251756297790333438427479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149501170865193555625618319 224251756297790333438427479)
    ·
      refine ⟨336377634446685500157641219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224251756297790333438427479 336377634446685500157641219)
      ·
        refine ⟨504566451670028250236461829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336377634446685500157641219 504566451670028250236461829)
        ·
          refine ⟨94606209688130296919336593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 504566451670028250236461829 94606209688130296919336593)
          ·
            refine ⟨70954657266097722689502445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94606209688130296919336593 70954657266097722689502445)
            ·
              refine ⟨26607996474786646008563417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70954657266097722689502445 26607996474786646008563417)
              ·
                refine ⟨19955997356089984506422563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26607996474786646008563417 19955997356089984506422563)
                ·
                  refine ⟨29933996034134976759633845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19955997356089984506422563 29933996034134976759633845)
                  ·
                    refine ⟨2806312128200154071215673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29933996034134976759633845 2806312128200154071215673)
                    ·
                      refine ⟨2104734096150115553411755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2806312128200154071215673 2104734096150115553411755)
                      ·
                        rfl

theorem cell23_4098955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 5, 2].length) (baseStart_4098955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4098955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4098955 prefixEnd_4098955 := by exact prefixLift 4098955
  have htrace : WordTrace (prefixWord ++ tailWord_4098955) baseStart_4098955 baseEnd_4098955 := by
    simpa [prefixWord, tailWord_4098955, baseEnd_4098955] using wordTrace_append hprefix tailTrace_4098955
  have hstable : (prefixWord ++ tailWord_4098955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098955).length < 2 ^ (prefixWord ++ tailWord_4098955).sum := by decide
  have hdescent : baseEnd_4098955 < baseStart_4098955 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098965 : List Nat := [1, 3, 2, 1, 1, 4, 1, 4, 1, 5]
def baseStart_4098965 : Nat := 118140960795 + 4098965 * 2 ^ 59
def prefixEnd_4098965 : Nat := 4983230072969 + 3 ^ 40 * 4098965 * 2
def baseEnd_4098965 : Nat := 701579743652220171428903

theorem tailTrace_4098965 : CollatzResearch.WordTrace tailWord_4098965 prefixEnd_4098965 701579743652220171428903 := by
  unfold tailWord_4098965
  simp only [CollatzResearch.WordTrace]
  refine ⟨149501535595157327333482349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99667690396771551555654899 149501535595157327333482349)
  ·
    refine ⟨56063075848183997750055881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149501535595157327333482349 56063075848183997750055881)
    ·
      refine ⟨42047306886137998312541911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56063075848183997750055881 42047306886137998312541911)
      ·
        refine ⟨63070960329206997468812867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42047306886137998312541911 63070960329206997468812867)
        ·
          refine ⟨94606440493810496203219301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63070960329206997468812867 94606440493810496203219301)
          ·
            refine ⟨17738707592589468038103619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94606440493810496203219301 17738707592589468038103619)
            ·
              refine ⟨26608061388884202057155429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17738707592589468038103619 26608061388884202057155429)
              ·
                refine ⟨4989011510415787885716643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26608061388884202057155429 4989011510415787885716643)
                ·
                  refine ⟨7483517265623681828574965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4989011510415787885716643 7483517265623681828574965)
                  ·
                    refine ⟨701579743652220171428903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7483517265623681828574965 701579743652220171428903)
                    ·
                      rfl

theorem cell23_4098965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 4, 1, 5].length) (baseStart_4098965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4098965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4098965 prefixEnd_4098965 := by exact prefixLift 4098965
  have htrace : WordTrace (prefixWord ++ tailWord_4098965) baseStart_4098965 baseEnd_4098965 := by
    simpa [prefixWord, tailWord_4098965, baseEnd_4098965] using wordTrace_append hprefix tailTrace_4098965
  have hstable : (prefixWord ++ tailWord_4098965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098965).length < 2 ^ (prefixWord ++ tailWord_4098965).sum := by decide
  have hdescent : baseEnd_4098965 < baseStart_4098965 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098979 : List Nat := [1, 1, 1, 4, 1, 2, 5, 3, 1, 1, 3]
def baseStart_4098979 : Nat := 118140960795 + 4098979 * 2 ^ 59
def prefixEnd_4098979 : Nat := 4983230072969 + 3 ^ 40 * 4098979 * 2
def baseEnd_4098979 : Nat := 2104746419685823459511645

theorem tailTrace_4098979 : CollatzResearch.WordTrace tailWord_4098979 prefixEnd_4098979 2104746419685823459511645 := by
  unfold tailWord_4098979
  simp only [CollatzResearch.WordTrace]
  refine ⟨149502046217106607724491991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99668030811404405149661327 149502046217106607724491991)
  ·
    refine ⟨224253069325659911586737987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149502046217106607724491991 224253069325659911586737987)
    ·
      refine ⟨336379603988489867380106981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224253069325659911586737987 336379603988489867380106981)
      ·
        refine ⟨63071175747841850133770059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 336379603988489867380106981 63071175747841850133770059)
        ·
          refine ⟨94606763621762775200655089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63071175747841850133770059 94606763621762775200655089)
          ·
            refine ⟨70955072716322081400491317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94606763621762775200655089 70955072716322081400491317)
            ·
              refine ⟨6652038067155195131296061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70955072716322081400491317 6652038067155195131296061)
              ·
                refine ⟨2494514275183198174236023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6652038067155195131296061 2494514275183198174236023)
                ·
                  refine ⟨3741771412774797261354035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2494514275183198174236023 3741771412774797261354035)
                  ·
                    refine ⟨5612657119162195892031053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3741771412774797261354035 5612657119162195892031053)
                    ·
                      refine ⟨2104746419685823459511645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5612657119162195892031053 2104746419685823459511645)
                      ·
                        rfl

theorem cell23_4098979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 3, 1, 1, 3].length) (baseStart_4098979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4098979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4098979 prefixEnd_4098979 := by exact prefixLift 4098979
  have htrace : WordTrace (prefixWord ++ tailWord_4098979) baseStart_4098979 baseEnd_4098979 := by
    simpa [prefixWord, tailWord_4098979, baseEnd_4098979] using wordTrace_append hprefix tailTrace_4098979
  have hstable : (prefixWord ++ tailWord_4098979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098979).length < 2 ^ (prefixWord ++ tailWord_4098979).sum := by decide
  have hdescent : baseEnd_4098979 < baseStart_4098979 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098985 : List Nat := [1, 2, 1, 1, 1, 1, 5, 5, 1, 1, 4]
def baseStart_4098985 : Nat := 118140960795 + 4098985 * 2 ^ 59
def prefixEnd_4098985 : Nat := 4983230072969 + 3 ^ 40 * 4098985 * 2
def baseEnd_4098985 : Nat := 2104749500569750436036617

theorem tailTrace_4098985 : CollatzResearch.WordTrace tailWord_4098985 prefixEnd_4098985 2104749500569750436036617 := by
  unfold tailWord_4098985
  simp only [CollatzResearch.WordTrace]
  refine ⟨149502265055084870749210409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99668176703389913832806939 149502265055084870749210409)
  ·
    refine ⟨112126698791313653061907807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149502265055084870749210409 112126698791313653061907807)
    ·
      refine ⟨168190048186970479592861711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112126698791313653061907807 168190048186970479592861711)
      ·
        refine ⟨252285072280455719389292567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168190048186970479592861711 252285072280455719389292567)
        ·
          refine ⟨378427608420683579083938851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252285072280455719389292567 378427608420683579083938851)
          ·
            refine ⟨567641412631025368625908277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378427608420683579083938851 567641412631025368625908277)
            ·
              refine ⟨53216382434158628308678901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 567641412631025368625908277 53216382434158628308678901)
              ·
                refine ⟨4989035853202371403938647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53216382434158628308678901 4989035853202371403938647)
                ·
                  refine ⟨7483553779803557105907971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4989035853202371403938647 7483553779803557105907971)
                  ·
                    refine ⟨11225330669705335658861957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7483553779803557105907971 11225330669705335658861957)
                    ·
                      refine ⟨2104749500569750436036617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11225330669705335658861957 2104749500569750436036617)
                      ·
                        rfl

theorem cell23_4098985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 5, 1, 1, 4].length) (baseStart_4098985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4098985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4098985 prefixEnd_4098985 := by exact prefixLift 4098985
  have htrace : WordTrace (prefixWord ++ tailWord_4098985) baseStart_4098985 baseEnd_4098985 := by
    simpa [prefixWord, tailWord_4098985, baseEnd_4098985] using wordTrace_append hprefix tailTrace_4098985
  have hstable : (prefixWord ++ tailWord_4098985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098985).length < 2 ^ (prefixWord ++ tailWord_4098985).sum := by decide
  have hdescent : baseEnd_4098985 < baseStart_4098985 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098988 : List Nat := [2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 5]
def baseStart_4098988 : Nat := 118140960795 + 4098988 * 2 ^ 59
def prefixEnd_4098988 : Nat := 4983230072969 + 3 ^ 40 * 4098988 * 2
def baseEnd_4098988 : Nat := 2104751041011713924299103

theorem tailTrace_4098988 : CollatzResearch.WordTrace tailWord_4098988 prefixEnd_4098988 2104751041011713924299103 := by
  unfold tailWord_4098988
  simp only [CollatzResearch.WordTrace]
  refine ⟨74751187237037001130784809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99668249649382668174379745 74751187237037001130784809)
  ·
    refine ⟨56063390427777750848088607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74751187237037001130784809 56063390427777750848088607)
    ·
      refine ⟨84095085641666626272132911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56063390427777750848088607 84095085641666626272132911)
      ·
        refine ⟨126142628462499939408199367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84095085641666626272132911 126142628462499939408199367)
        ·
          refine ⟨189213942693749909112299051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126142628462499939408199367 189213942693749909112299051)
          ·
            refine ⟨283820914040624863668448577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189213942693749909112299051 283820914040624863668448577)
            ·
              refine ⟨212865685530468647751336433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283820914040624863668448577 212865685530468647751336433)
              ·
                refine ⟨159649264147851485813502325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 212865685530468647751336433 159649264147851485813502325)
                ·
                  refine ⟨14967118513861076795015843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 159649264147851485813502325 14967118513861076795015843)
                  ·
                    refine ⟨22450677770791615192523765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14967118513861076795015843 22450677770791615192523765)
                    ·
                      refine ⟨2104751041011713924299103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22450677770791615192523765 2104751041011713924299103)
                      ·
                        rfl

theorem cell23_4098988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 5].length) (baseStart_4098988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4098988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4098988 prefixEnd_4098988 := by exact prefixLift 4098988
  have htrace : WordTrace (prefixWord ++ tailWord_4098988) baseStart_4098988 baseEnd_4098988 := by
    simpa [prefixWord, tailWord_4098988, baseEnd_4098988] using wordTrace_append hprefix tailTrace_4098988
  have hstable : (prefixWord ++ tailWord_4098988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098988).length < 2 ^ (prefixWord ++ tailWord_4098988).sum := by decide
  have hdescent : baseEnd_4098988 < baseStart_4098988 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098996 : List Nat := [2, 5, 2, 1, 1, 1, 3, 1, 3, 1, 3]
def baseStart_4098996 : Nat := 118140960795 + 4098996 * 2 ^ 59
def prefixEnd_4098996 : Nat := 4983230072969 + 3 ^ 40 * 4098996 * 2
def baseEnd_4098996 : Nat := 2104755148856949892999067

theorem tailTrace_4098996 : CollatzResearch.WordTrace tailWord_4098996 prefixEnd_4098996 2104755148856949892999067 := by
  unfold tailWord_4098996
  simp only [CollatzResearch.WordTrace]
  refine ⟨74751333129022509813930421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99668444172030013085240561 74751333129022509813930421)
  ·
    refine ⟨7007937480845860295055977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74751333129022509813930421 7007937480845860295055977)
    ·
      refine ⟨5255953110634395221291983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7007937480845860295055977 5255953110634395221291983)
      ·
        refine ⟨7883929665951592831937975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5255953110634395221291983 7883929665951592831937975)
        ·
          refine ⟨11825894498927389247906963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7883929665951592831937975 11825894498927389247906963)
          ·
            refine ⟨17738841748391083871860445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11825894498927389247906963 17738841748391083871860445)
            ·
              refine ⟨6652065655646656451947667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17738841748391083871860445 6652065655646656451947667)
              ·
                refine ⟨9978098483469984677921501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6652065655646656451947667 9978098483469984677921501)
                ·
                  refine ⟨3741786931301244254220563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9978098483469984677921501 3741786931301244254220563)
                  ·
                    refine ⟨5612680396951866381330845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3741786931301244254220563 5612680396951866381330845)
                    ·
                      refine ⟨2104755148856949892999067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5612680396951866381330845 2104755148856949892999067)
                      ·
                        rfl

theorem cell23_4098996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_4098996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4098996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4098996 prefixEnd_4098996 := by exact prefixLift 4098996
  have htrace : WordTrace (prefixWord ++ tailWord_4098996) baseStart_4098996 baseEnd_4098996 := by
    simpa [prefixWord, tailWord_4098996, baseEnd_4098996] using wordTrace_append hprefix tailTrace_4098996
  have hstable : (prefixWord ++ tailWord_4098996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098996).length < 2 ^ (prefixWord ++ tailWord_4098996).sum := by decide
  have hdescent : baseEnd_4098996 < baseStart_4098996 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099008 : List Nat := [2, 1, 1, 2, 3, 3, 1, 10]
def baseStart_4099008 : Nat := 118140960795 + 4099008 * 2 ^ 59
def prefixEnd_4099008 : Nat := 4983230072969 + 3 ^ 40 * 4099008 * 2
def baseEnd_4099008 : Nat := 77954122615733475779593

theorem tailTrace_4099008 : CollatzResearch.WordTrace tailWord_4099008 prefixEnd_4099008 77954122615733475779593 := by
  unfold tailWord_4099008
  simp only [CollatzResearch.WordTrace]
  refine ⟨74751551967000772838648839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99668735956001030451531785 74751551967000772838648839)
  ·
    refine ⟨112127327950501159257973259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74751551967000772838648839 112127327950501159257973259)
    ·
      refine ⟨168190991925751738886959889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112127327950501159257973259 168190991925751738886959889)
      ·
        refine ⟨126143243944313804165219917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168190991925751738886959889 126143243944313804165219917)
        ·
          refine ⟨47303716479117676561957469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126143243944313804165219917 47303716479117676561957469)
          ·
            refine ⟨17738893679669128710734051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47303716479117676561957469 17738893679669128710734051)
            ·
              refine ⟨26608340519503693066101077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17738893679669128710734051 26608340519503693066101077)
              ·
                refine ⟨77954122615733475779593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 26608340519503693066101077 77954122615733475779593)
                ·
                  rfl

theorem cell23_4099008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 10].length) (baseStart_4099008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4099008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4099008 prefixEnd_4099008 := by exact prefixLift 4099008
  have htrace : WordTrace (prefixWord ++ tailWord_4099008) baseStart_4099008 baseEnd_4099008 := by
    simpa [prefixWord, tailWord_4099008, baseEnd_4099008] using wordTrace_append hprefix tailTrace_4099008
  have hstable : (prefixWord ++ tailWord_4099008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099008).length < 2 ^ (prefixWord ++ tailWord_4099008).sum := by decide
  have hdescent : baseEnd_4099008 < baseStart_4099008 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099022 : List Nat := [4, 1, 1, 1, 2, 4, 1, 1, 3, 2, 3]
def baseStart_4099022 : Nat := 118140960795 + 4099022 * 2 ^ 59
def prefixEnd_4099022 : Nat := 4983230072969 + 3 ^ 40 * 4099022 * 2
def baseEnd_4099022 : Nat := 2104768499353966791273947

theorem tailTrace_4099022 : CollatzResearch.WordTrace tailWord_4099022 prefixEnd_4099022 2104768499353966791273947 := by
  unfold tailWord_4099022
  simp only [CollatzResearch.WordTrace]
  refine ⟨18687951819493853258538415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99669076370633884045538213 18687951819493853258538415)
  ·
    refine ⟨28031927729240779887807623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18687951819493853258538415 28031927729240779887807623)
    ·
      refine ⟨42047891593861169831711435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28031927729240779887807623 42047891593861169831711435)
      ·
        refine ⟨63071837390791754747567153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42047891593861169831711435 63071837390791754747567153)
        ·
          refine ⟨47303878043093816060675365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63071837390791754747567153 47303878043093816060675365)
          ·
            refine ⟨8869477133080090511376631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47303878043093816060675365 8869477133080090511376631)
            ·
              refine ⟨13304215699620135767064947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8869477133080090511376631 13304215699620135767064947)
              ·
                refine ⟨19956323549430203650597421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13304215699620135767064947 19956323549430203650597421)
                ·
                  refine ⟨7483621331036326368974033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19956323549430203650597421 7483621331036326368974033)
                  ·
                    refine ⟨5612715998277244776730525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7483621331036326368974033 5612715998277244776730525)
                    ·
                      refine ⟨2104768499353966791273947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5612715998277244776730525 2104768499353966791273947)
                      ·
                        rfl

theorem cell23_4099022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 3, 2, 3].length) (baseStart_4099022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4099022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4099022 prefixEnd_4099022 := by exact prefixLift 4099022
  have htrace : WordTrace (prefixWord ++ tailWord_4099022) baseStart_4099022 baseEnd_4099022 := by
    simpa [prefixWord, tailWord_4099022, baseEnd_4099022] using wordTrace_append hprefix tailTrace_4099022
  have hstable : (prefixWord ++ tailWord_4099022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099022).length < 2 ^ (prefixWord ++ tailWord_4099022).sum := by decide
  have hdescent : baseEnd_4099022 < baseStart_4099022 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099039 : List Nat := [1, 1, 2, 3, 6, 1, 1, 1, 1, 1, 5]
def baseStart_4099039 : Nat := 118140960795 + 4099039 * 2 ^ 59
def prefixEnd_4099039 : Nat := 4983230072969 + 3 ^ 40 * 4099039 * 2
def baseEnd_4099039 : Nat := 2104777228525093224761369

theorem tailTrace_4099039 : CollatzResearch.WordTrace tailWord_4099039 prefixEnd_4099039 2104777228525093224761369 := by
  unfold tailWord_4099039
  simp only [CollatzResearch.WordTrace]
  refine ⟨149504234596889237971676171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99669489731259491981117447 149504234596889237971676171)
  ·
    refine ⟨224256351895333856957514257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149504234596889237971676171 224256351895333856957514257)
    ·
      refine ⟨168192263921500392718135693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224256351895333856957514257 168192263921500392718135693)
      ·
        refine ⟨63072098970562647269300885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168192263921500392718135693 63072098970562647269300885)
        ·
          refine ⟨2956504639245124090748479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 63072098970562647269300885 2956504639245124090748479)
          ·
            refine ⟨4434756958867686136122719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2956504639245124090748479 4434756958867686136122719)
            ·
              refine ⟨6652135438301529204184079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4434756958867686136122719 6652135438301529204184079)
              ·
                refine ⟨9978203157452293806276119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6652135438301529204184079 9978203157452293806276119)
                ·
                  refine ⟨14967304736178440709414179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9978203157452293806276119 14967304736178440709414179)
                  ·
                    refine ⟨22450957104267661064121269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14967304736178440709414179 22450957104267661064121269)
                    ·
                      refine ⟨2104777228525093224761369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22450957104267661064121269 2104777228525093224761369)
                      ·
                        rfl

theorem cell23_4099039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 1, 1, 1, 5].length) (baseStart_4099039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4099039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4099039 prefixEnd_4099039 := by exact prefixLift 4099039
  have htrace : WordTrace (prefixWord ++ tailWord_4099039) baseStart_4099039 baseEnd_4099039 := by
    simpa [prefixWord, tailWord_4099039, baseEnd_4099039] using wordTrace_append hprefix tailTrace_4099039
  have hstable : (prefixWord ++ tailWord_4099039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099039).length < 2 ^ (prefixWord ++ tailWord_4099039).sum := by decide
  have hdescent : baseEnd_4099039 < baseStart_4099039 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099079 : List Nat := [1, 1, 4, 3, 1, 1, 2, 4, 1, 3, 2]
def baseStart_4099079 : Nat := 118140960795 + 4099079 * 2 ^ 59
def prefixEnd_4099079 : Nat := 4983230072969 + 3 ^ 40 * 4099079 * 2
def baseEnd_4099079 : Nat := 2104797767751273068261185

theorem tailTrace_4099079 : CollatzResearch.WordTrace tailWord_4099079 prefixEnd_4099079 2104797767751273068261185 := by
  unfold tailWord_4099079
  simp only [CollatzResearch.WordTrace]
  refine ⟨149505693516744324803132291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99670462344496216535421527 149505693516744324803132291)
  ·
    refine ⟨224258540275116487204698437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149505693516744324803132291 224258540275116487204698437)
    ·
      refine ⟨42048476301584341350880957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 224258540275116487204698437 42048476301584341350880957)
      ·
        refine ⟨15768178613094128006580359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42048476301584341350880957 15768178613094128006580359)
        ·
          refine ⟨23652267919641192009870539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15768178613094128006580359 23652267919641192009870539)
          ·
            refine ⟨35478401879461788014805809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23652267919641192009870539 35478401879461788014805809)
            ·
              refine ⟨26608801409596341011104357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35478401879461788014805809 26608801409596341011104357)
              ·
                refine ⟨4989150264299313939582067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26608801409596341011104357 4989150264299313939582067)
                ·
                  refine ⟨7483725396448970909373101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4989150264299313939582067 7483725396448970909373101)
                  ·
                    refine ⟨2806397023668364091014913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7483725396448970909373101 2806397023668364091014913)
                    ·
                      refine ⟨2104797767751273068261185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2806397023668364091014913 2104797767751273068261185)
                      ·
                        rfl

theorem cell23_4099079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 4, 1, 3, 2].length) (baseStart_4099079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4099079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4099079 prefixEnd_4099079 := by exact prefixLift 4099079
  have htrace : WordTrace (prefixWord ++ tailWord_4099079) baseStart_4099079 baseEnd_4099079 := by
    simpa [prefixWord, tailWord_4099079, baseEnd_4099079] using wordTrace_append hprefix tailTrace_4099079
  have hstable : (prefixWord ++ tailWord_4099079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099079).length < 2 ^ (prefixWord ++ tailWord_4099079).sum := by decide
  have hdescent : baseEnd_4099079 < baseStart_4099079 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099096 : List Nat := [2, 1, 2, 3, 2, 2, 4, 1, 1, 3, 2]
def baseStart_4099096 : Nat := 118140960795 + 4099096 * 2 ^ 59
def prefixEnd_4099096 : Nat := 4983230072969 + 3 ^ 40 * 4099096 * 2
def baseEnd_4099096 : Nat := 2104806496922399501748607

theorem tailTrace_4099096 : CollatzResearch.WordTrace tailWord_4099096 prefixEnd_4099096 2104806496922399501748607 := by
  unfold tailWord_4099096
  simp only [CollatzResearch.WordTrace]
  refine ⟨74753156778841368353250571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99670875705121824471000761 74753156778841368353250571)
  ·
    refine ⟨112129735168262052529875857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74753156778841368353250571 112129735168262052529875857)
    ·
      refine ⟨84097301376196539397406893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112129735168262052529875857 84097301376196539397406893)
      ·
        refine ⟨31536488016073702274027585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84097301376196539397406893 31536488016073702274027585)
        ·
          refine ⟨23652366012055276705520689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31536488016073702274027585 23652366012055276705520689)
          ·
            refine ⟨17739274509041457529140517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23652366012055276705520689 17739274509041457529140517)
            ·
              refine ⟨3326113970445273286713847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17739274509041457529140517 3326113970445273286713847)
              ·
                refine ⟨4989170955667909930070771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3326113970445273286713847 4989170955667909930070771)
                ·
                  refine ⟨7483756433501864895106157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4989170955667909930070771 7483756433501864895106157)
                  ·
                    refine ⟨2806408662563199335664809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7483756433501864895106157 2806408662563199335664809)
                    ·
                      refine ⟨2104806496922399501748607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2806408662563199335664809 2104806496922399501748607)
                      ·
                        rfl

theorem cell23_4099096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 4, 1, 1, 3, 2].length) (baseStart_4099096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4099096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4099096 prefixEnd_4099096 := by exact prefixLift 4099096
  have htrace : WordTrace (prefixWord ++ tailWord_4099096) baseStart_4099096 baseEnd_4099096 := by
    simpa [prefixWord, tailWord_4099096, baseEnd_4099096] using wordTrace_append hprefix tailTrace_4099096
  have hstable : (prefixWord ++ tailWord_4099096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099096).length < 2 ^ (prefixWord ++ tailWord_4099096).sum := by decide
  have hdescent : baseEnd_4099096 < baseStart_4099096 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099109 : List Nat := [1, 3, 1, 2, 2, 2, 3, 1, 4, 2, 2]
def baseStart_4099109 : Nat := 118140960795 + 4099109 * 2 ^ 59
def prefixEnd_4099109 : Nat := 4983230072969 + 3 ^ 40 * 4099109 * 2
def baseEnd_4099109 : Nat := 2104813172170907950886047

theorem tailTrace_4099109 : CollatzResearch.WordTrace tailWord_4099109 prefixEnd_4099109 2104813172170907950886047 := by
  unfold tailWord_4099109
  simp only [CollatzResearch.WordTrace]
  refine ⟨149506787706635639926724381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99671191804423759951149587 149506787706635639926724381)
  ·
    refine ⟨56065045389988364972521643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149506787706635639926724381 56065045389988364972521643)
    ·
      refine ⟨84097568084982547458782465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56065045389988364972521643 84097568084982547458782465)
      ·
        refine ⟨63073176063736910594086849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84097568084982547458782465 63073176063736910594086849)
        ·
          refine ⟨47304882047802682945565137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63073176063736910594086849 47304882047802682945565137)
          ·
            refine ⟨35478661535852012209173853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47304882047802682945565137 35478661535852012209173853)
            ·
              refine ⟨13304498075944504578440195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35478661535852012209173853 13304498075944504578440195)
              ·
                refine ⟨19956747113916756867660293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13304498075944504578440195 19956747113916756867660293)
                ·
                  refine ⟨3741890083859391912686305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19956747113916756867660293 3741890083859391912686305)
                  ·
                    refine ⟨2806417562894543934514729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3741890083859391912686305 2806417562894543934514729)
                    ·
                      refine ⟨2104813172170907950886047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2806417562894543934514729 2104813172170907950886047)
                      ·
                        rfl

theorem cell23_4099109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 4, 2, 2].length) (baseStart_4099109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4099109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4099109 prefixEnd_4099109 := by exact prefixLift 4099109
  have htrace : WordTrace (prefixWord ++ tailWord_4099109) baseStart_4099109 baseEnd_4099109 := by
    simpa [prefixWord, tailWord_4099109, baseEnd_4099109] using wordTrace_append hprefix tailTrace_4099109
  have hstable : (prefixWord ++ tailWord_4099109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099109).length < 2 ^ (prefixWord ++ tailWord_4099109).sum := by decide
  have hdescent : baseEnd_4099109 < baseStart_4099109 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099115 : List Nat := [1, 1, 1, 1, 2, 1, 8, 1, 7]
def baseStart_4099115 : Nat := 118140960795 + 4099115 * 2 ^ 59
def prefixEnd_4099115 : Nat := 4983230072969 + 3 ^ 40 * 4099115 * 2
def baseEnd_4099115 : Nat := 233868472561648325267891

theorem tailTrace_4099115 : CollatzResearch.WordTrace tailWord_4099115 prefixEnd_4099115 233868472561648325267891 := by
  unfold tailWord_4099115
  simp only [CollatzResearch.WordTrace]
  refine ⟨149507006544613902951442799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99671337696409268634295199 149507006544613902951442799)
  ·
    refine ⟨224260509816920854427164199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149507006544613902951442799 224260509816920854427164199)
    ·
      refine ⟨336390764725381281640746299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224260509816920854427164199 336390764725381281640746299)
      ·
        refine ⟨504586147088071922461119449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336390764725381281640746299 504586147088071922461119449)
        ·
          refine ⟨378439610316053941845839587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 504586147088071922461119449 378439610316053941845839587)
          ·
            refine ⟨567659415474080912768759381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378439610316053941845839587 567659415474080912768759381)
            ·
              refine ⟨6652258775086885696508899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 567659415474080912768759381 6652258775086885696508899)
              ·
                refine ⟨9978388162630328544763349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6652258775086885696508899 9978388162630328544763349)
                ·
                  refine ⟨233868472561648325267891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9978388162630328544763349 233868472561648325267891)
                  ·
                    rfl

theorem cell23_4099115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 1, 7].length) (baseStart_4099115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4099115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4099115 prefixEnd_4099115 := by exact prefixLift 4099115
  have htrace : WordTrace (prefixWord ++ tailWord_4099115) baseStart_4099115 baseEnd_4099115 := by
    simpa [prefixWord, tailWord_4099115, baseEnd_4099115] using wordTrace_append hprefix tailTrace_4099115
  have hstable : (prefixWord ++ tailWord_4099115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099115).length < 2 ^ (prefixWord ++ tailWord_4099115).sum := by decide
  have hdescent : baseEnd_4099115 < baseStart_4099115 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099126 : List Nat := [5, 1, 2, 1, 1, 2, 3, 1, 1, 4, 2]
def baseStart_4099126 : Nat := 118140960795 + 4099126 * 2 ^ 59
def prefixEnd_4099126 : Nat := 4983230072969 + 3 ^ 40 * 4099126 * 2
def baseEnd_4099126 : Nat := 2104821901342034384373469

theorem tailTrace_4099126 : CollatzResearch.WordTrace tailWord_4099126 prefixEnd_4099126 2104821901342034384373469 := by
  unfold tailWord_4099126
  simp only [CollatzResearch.WordTrace]
  refine ⟨9344212984223378239380827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99671605165049367886728821 9344212984223378239380827)
  ·
    refine ⟨14016319476335067359071241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9344212984223378239380827 14016319476335067359071241)
    ·
      refine ⟨10512239607251300519303431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14016319476335067359071241 10512239607251300519303431)
      ·
        refine ⟨15768359410876950778955147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10512239607251300519303431 15768359410876950778955147)
        ·
          refine ⟨23652539116315426168432721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15768359410876950778955147 23652539116315426168432721)
          ·
            refine ⟨17739404337236569626324541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23652539116315426168432721 17739404337236569626324541)
            ·
              refine ⟨6652276626463713609871703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17739404337236569626324541 6652276626463713609871703)
              ·
                refine ⟨9978414939695570414807555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6652276626463713609871703 9978414939695570414807555)
                ·
                  refine ⟨14967622409543355622211333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9978414939695570414807555 14967622409543355622211333)
                  ·
                    refine ⟨2806429201789379179164625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14967622409543355622211333 2806429201789379179164625)
                    ·
                      refine ⟨2104821901342034384373469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2806429201789379179164625 2104821901342034384373469)
                      ·
                        rfl

theorem cell23_4099126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 1, 1, 4, 2].length) (baseStart_4099126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4099126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4099126 prefixEnd_4099126 := by exact prefixLift 4099126
  have htrace : WordTrace (prefixWord ++ tailWord_4099126) baseStart_4099126 baseEnd_4099126 := by
    simpa [prefixWord, tailWord_4099126, baseEnd_4099126] using wordTrace_append hprefix tailTrace_4099126
  have hstable : (prefixWord ++ tailWord_4099126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099126).length < 2 ^ (prefixWord ++ tailWord_4099126).sum := by decide
  have hdescent : baseEnd_4099126 < baseStart_4099126 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099166 : List Nat := [4, 4, 1, 1, 1, 1, 3, 1, 7]
def baseStart_4099166 : Nat := 118140960795 + 4099166 * 2 ^ 59
def prefixEnd_4099166 : Nat := 4983230072969 + 3 ^ 40 * 4099166 * 2
def baseEnd_4099166 : Nat := 233871382285357136430365

theorem tailTrace_4099166 : CollatzResearch.WordTrace tailWord_4099166 prefixEnd_4099166 233871382285357136430365 := by
  unfold tailWord_4099166
  simp only [CollatzResearch.WordTrace]
  refine ⟨18688608333428642332693669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99672577778286092441032901 18688608333428642332693669)
  ·
    refine ⟨3504114062517870437380063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18688608333428642332693669 3504114062517870437380063)
    ·
      refine ⟨5256171093776805656070095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3504114062517870437380063 5256171093776805656070095)
      ·
        refine ⟨7884256640665208484105143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5256171093776805656070095 7884256640665208484105143)
        ·
          refine ⟨11826384960997812726157715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7884256640665208484105143 11826384960997812726157715)
          ·
            refine ⟨17739577441496719089236573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11826384960997812726157715 17739577441496719089236573)
            ·
              refine ⟨6652341540561269658463715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17739577441496719089236573 6652341540561269658463715)
              ·
                refine ⟨9978512310841904487695573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6652341540561269658463715 9978512310841904487695573)
                ·
                  refine ⟨233871382285357136430365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9978512310841904487695573 233871382285357136430365)
                  ·
                    rfl

theorem cell23_4099166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_4099166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4099166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4099166 prefixEnd_4099166 := by exact prefixLift 4099166
  have htrace : WordTrace (prefixWord ++ tailWord_4099166) baseStart_4099166 baseEnd_4099166 := by
    simpa [prefixWord, tailWord_4099166, baseEnd_4099166] using wordTrace_append hprefix tailTrace_4099166
  have hstable : (prefixWord ++ tailWord_4099166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099166).length < 2 ^ (prefixWord ++ tailWord_4099166).sum := by decide
  have hdescent : baseEnd_4099166 < baseStart_4099166 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099192 : List Nat := [2, 1, 2, 1, 1, 1, 4, 4, 3, 4]
def baseStart_4099192 : Nat := 118140960795 + 4099192 * 2 ^ 59
def prefixEnd_4099192 : Nat := 4983230072969 + 3 ^ 40 * 4099192 * 2
def baseEnd_4099192 : Nat := 701618597021743708716055

theorem tailTrace_4099192 : CollatzResearch.WordTrace tailWord_4099192 prefixEnd_4099192 701618597021743708716055 := by
  unfold tailWord_4099192
  simp only [CollatzResearch.WordTrace]
  refine ⟨74754907482667472550997915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99673209976889963401330553 74754907482667472550997915)
  ·
    refine ⟨112132361224001208826496873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74754907482667472550997915 112132361224001208826496873)
    ·
      refine ⟨84099270918000906619872655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112132361224001208826496873 84099270918000906619872655)
      ·
        refine ⟨126148906377001359929808983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84099270918000906619872655 126148906377001359929808983)
        ·
          refine ⟨189223359565502039894713475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126148906377001359929808983 189223359565502039894713475)
          ·
            refine ⟨283835039348253059842070213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189223359565502039894713475 283835039348253059842070213)
            ·
              refine ⟨53219069877797448720388165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 283835039348253059842070213 53219069877797448720388165)
              ·
                refine ⟨9978575602087021635072781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53219069877797448720388165 9978575602087021635072781)
                ·
                  refine ⟨3741965850782633113152293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9978575602087021635072781 3741965850782633113152293)
                  ·
                    refine ⟨701618597021743708716055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3741965850782633113152293 701618597021743708716055)
                    ·
                      rfl

theorem cell23_4099192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 4, 3, 4].length) (baseStart_4099192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4099192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4099192 prefixEnd_4099192 := by exact prefixLift 4099192
  have htrace : WordTrace (prefixWord ++ tailWord_4099192) baseStart_4099192 baseEnd_4099192 := by
    simpa [prefixWord, tailWord_4099192, baseEnd_4099192] using wordTrace_append hprefix tailTrace_4099192
  have hstable : (prefixWord ++ tailWord_4099192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099192).length < 2 ^ (prefixWord ++ tailWord_4099192).sum := by decide
  have hdescent : baseEnd_4099192 < baseStart_4099192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099195 : List Nat := [1, 1, 1, 1, 1, 4, 1, 3, 2, 4, 4]
def baseStart_4099195 : Nat := 118140960795 + 4099195 * 2 ^ 59
def prefixEnd_4099195 : Nat := 4983230072969 + 3 ^ 40 * 4099195 * 2
def baseEnd_4099195 : Nat := 2104857331507194614410651

theorem tailTrace_4099195 : CollatzResearch.WordTrace tailWord_4099195 prefixEnd_4099195 2104857331507194614410651 := by
  unfold tailWord_4099195
  simp only [CollatzResearch.WordTrace]
  refine ⟨149509924384324076614355039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99673282922882717742903359 149509924384324076614355039)
  ·
    refine ⟨224264886576486114921532559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149509924384324076614355039 224264886576486114921532559)
    ·
      refine ⟨336397329864729172382298839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224264886576486114921532559 336397329864729172382298839)
      ·
        refine ⟨504595994797093758573448259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336397329864729172382298839 504595994797093758573448259)
        ·
          refine ⟨756893992195640637860172389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 504595994797093758573448259 756893992195640637860172389)
          ·
            refine ⟨141917623536682619598782323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 756893992195640637860172389 141917623536682619598782323)
            ·
              refine ⟨212876435305023929398173485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141917623536682619598782323 212876435305023929398173485)
              ·
                refine ⟨79828663239383973524315057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 212876435305023929398173485 79828663239383973524315057)
                ·
                  refine ⟨59871497429537980143236293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79828663239383973524315057 59871497429537980143236293)
                  ·
                    refine ⟨11225905768038371276856805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59871497429537980143236293 11225905768038371276856805)
                    ·
                      refine ⟨2104857331507194614410651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11225905768038371276856805 2104857331507194614410651)
                      ·
                        rfl

theorem cell23_4099195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 4, 4].length) (baseStart_4099195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4099195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4099195 prefixEnd_4099195 := by exact prefixLift 4099195
  have htrace : WordTrace (prefixWord ++ tailWord_4099195) baseStart_4099195 baseEnd_4099195 := by
    simpa [prefixWord, tailWord_4099195, baseEnd_4099195] using wordTrace_append hprefix tailTrace_4099195
  have hstable : (prefixWord ++ tailWord_4099195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099195).length < 2 ^ (prefixWord ++ tailWord_4099195).sum := by decide
  have hdescent : baseEnd_4099195 < baseStart_4099195 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099239 : List Nat := [1, 1, 6, 2, 1, 1, 2, 3, 6]
def baseStart_4099239 : Nat := 118140960795 + 4099239 * 2 ^ 59
def prefixEnd_4099239 : Nat := 4983230072969 + 3 ^ 40 * 4099239 * 2
def baseEnd_4099239 : Nat := 233875547183999160251161

theorem tailTrace_4099239 : CollatzResearch.WordTrace tailWord_4099239 prefixEnd_4099239 233875547183999160251161 := by
  unfold tailWord_4099239
  simp only [CollatzResearch.WordTrace]
  refine ⟨149511529196164672128956771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99674352797443114752637847 149511529196164672128956771)
  ·
    refine ⟨224267293794247008193435157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149511529196164672128956771 224267293794247008193435157)
    ·
      refine ⟨10512529396605328509067273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 224267293794247008193435157 10512529396605328509067273)
      ·
        refine ⟨7884397047453996381800455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10512529396605328509067273 7884397047453996381800455)
        ·
          refine ⟨11826595571180994572700683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7884397047453996381800455 11826595571180994572700683)
          ·
            refine ⟨17739893356771491859051025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11826595571180994572700683 17739893356771491859051025)
            ·
              refine ⟨13304920017578618894288269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17739893356771491859051025 13304920017578618894288269)
              ·
                refine ⟨4989345006591982085358101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13304920017578618894288269 4989345006591982085358101)
                ·
                  refine ⟨233875547183999160251161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4989345006591982085358101 233875547183999160251161)
                  ·
                    rfl

theorem cell23_4099239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 3, 6].length) (baseStart_4099239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4099239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4099239 prefixEnd_4099239 := by exact prefixLift 4099239
  have htrace : WordTrace (prefixWord ++ tailWord_4099239) baseStart_4099239 baseEnd_4099239 := by
    simpa [prefixWord, tailWord_4099239, baseEnd_4099239] using wordTrace_append hprefix tailTrace_4099239
  have hstable : (prefixWord ++ tailWord_4099239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099239).length < 2 ^ (prefixWord ++ tailWord_4099239).sum := by decide
  have hdescent : baseEnd_4099239 < baseStart_4099239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099259 : List Nat := [1, 1, 1, 1, 1, 2, 4, 5, 2, 3, 2]
def baseStart_4099259 : Nat := 118140960795 + 4099259 * 2 ^ 59
def prefixEnd_4099259 : Nat := 4983230072969 + 3 ^ 40 * 4099259 * 2
def baseEnd_4099259 : Nat := 2104890194269082364010357

theorem tailTrace_4099259 : CollatzResearch.WordTrace tailWord_4099259 prefixEnd_4099259 2104890194269082364010357 := by
  unfold tailWord_4099259
  simp only [CollatzResearch.WordTrace]
  refine ⟨149512258656092215544684831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99674839104061477029789887 149512258656092215544684831)
  ·
    refine ⟨224268387984138323317027247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149512258656092215544684831 224268387984138323317027247)
    ·
      refine ⟨336402581976207484975540871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224268387984138323317027247 336402581976207484975540871)
      ·
        refine ⟨504603872964311227463311307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336402581976207484975540871 504603872964311227463311307)
        ·
          refine ⟨756905809446466841194966961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 504603872964311227463311307 756905809446466841194966961)
          ·
            refine ⟨567679357084850130896225221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 756905809446466841194966961 567679357084850130896225221)
            ·
              refine ⟨106439879453409399543042229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 567679357084850130896225221 106439879453409399543042229)
              ·
                refine ⟨9978738698757131207160209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106439879453409399543042229 9978738698757131207160209)
                ·
                  refine ⟨7484054024067848405370157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9978738698757131207160209 7484054024067848405370157)
                  ·
                    refine ⟨2806520259025443152013809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7484054024067848405370157 2806520259025443152013809)
                    ·
                      refine ⟨2104890194269082364010357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2806520259025443152013809 2104890194269082364010357)
                      ·
                        rfl

theorem cell23_4099259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5, 2, 3, 2].length) (baseStart_4099259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4099259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4099259 prefixEnd_4099259 := by exact prefixLift 4099259
  have htrace : WordTrace (prefixWord ++ tailWord_4099259) baseStart_4099259 baseEnd_4099259 := by
    simpa [prefixWord, tailWord_4099259, baseEnd_4099259] using wordTrace_append hprefix tailTrace_4099259
  have hstable : (prefixWord ++ tailWord_4099259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099259).length < 2 ^ (prefixWord ++ tailWord_4099259).sum := by decide
  have hdescent : baseEnd_4099259 < baseStart_4099259 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099306 : List Nat := [3, 1, 3, 1, 1, 4, 2, 2, 1, 1, 4]
def baseStart_4099306 : Nat := 118140960795 + 4099306 * 2 ^ 59
def prefixEnd_4099306 : Nat := 4983230072969 + 3 ^ 40 * 4099306 * 2
def baseEnd_4099306 : Nat := 2104914327859843680122641

theorem tailTrace_4099306 : CollatzResearch.WordTrace tailWord_4099306 prefixEnd_4099306 2104914327859843680122641 := by
  unfold tailWord_4099306
  simp only [CollatzResearch.WordTrace]
  refine ⟨37378493221730485642911443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99675981924614628381097181 37378493221730485642911443)
  ·
    refine ⟨56067739832595728464367165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37378493221730485642911443 56067739832595728464367165)
    ·
      refine ⟨21025402437223398174137687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56067739832595728464367165 21025402437223398174137687)
      ·
        refine ⟨31538103655835097261206531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21025402437223398174137687 31538103655835097261206531)
        ·
          refine ⟨47307155483752645891809797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31538103655835097261206531 47307155483752645891809797)
          ·
            refine ⟨8870091653203621104714337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47307155483752645891809797 8870091653203621104714337)
            ·
              refine ⟨6652568739902715828535753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8870091653203621104714337 6652568739902715828535753)
              ·
                refine ⟨4989426554927036871401815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6652568739902715828535753 4989426554927036871401815)
                ·
                  refine ⟨7484139832390555307102723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4989426554927036871401815 7484139832390555307102723)
                  ·
                    refine ⟨11226209748585832960654085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7484139832390555307102723 11226209748585832960654085)
                    ·
                      refine ⟨2104914327859843680122641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11226209748585832960654085 2104914327859843680122641)
                      ·
                        rfl

theorem cell23_4099306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 2, 1, 1, 4].length) (baseStart_4099306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4099306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4099306 prefixEnd_4099306 := by exact prefixLift 4099306
  have htrace : WordTrace (prefixWord ++ tailWord_4099306) baseStart_4099306 baseEnd_4099306 := by
    simpa [prefixWord, tailWord_4099306, baseEnd_4099306] using wordTrace_append hprefix tailTrace_4099306
  have hstable : (prefixWord ++ tailWord_4099306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099306).length < 2 ^ (prefixWord ++ tailWord_4099306).sum := by decide
  have hdescent : baseEnd_4099306 < baseStart_4099306 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099326 : List Nat := [4, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5]
def baseStart_4099326 : Nat := 118140960795 + 4099326 * 2 ^ 59
def prefixEnd_4099326 : Nat := 4983230072969 + 3 ^ 40 * 4099326 * 2
def baseEnd_4099326 : Nat := 2104924597472933601872549

theorem tailTrace_4099326 : CollatzResearch.WordTrace tailWord_4099326 prefixEnd_4099326 2104924597472933601872549 := by
  unfold tailWord_4099326
  simp only [CollatzResearch.WordTrace]
  refine ⟨18689337793356185748421729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99676468231232990658249221 18689337793356185748421729)
  ·
    refine ⟨14017003345017139311316297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18689337793356185748421729 14017003345017139311316297)
    ·
      refine ⟨10512752508762854483487223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14017003345017139311316297 10512752508762854483487223)
      ·
        refine ⟨15769128763144281725230835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10512752508762854483487223 15769128763144281725230835)
        ·
          refine ⟨23653693144716422587846253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15769128763144281725230835 23653693144716422587846253)
          ·
            refine ⟨8870134929268658470442345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23653693144716422587846253 8870134929268658470442345)
            ·
              refine ⟨6652601196951493852831759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8870134929268658470442345 6652601196951493852831759)
              ·
                refine ⟨9978901795427240779247639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6652601196951493852831759 9978901795427240779247639)
                ·
                  refine ⟨14968352693140861168871459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9978901795427240779247639 14968352693140861168871459)
                  ·
                    refine ⟨22452529039711291753307189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14968352693140861168871459 22452529039711291753307189)
                    ·
                      refine ⟨2104924597472933601872549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22452529039711291753307189 2104924597472933601872549)
                      ·
                        rfl

theorem cell23_4099326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_4099326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4099326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4099326 prefixEnd_4099326 := by exact prefixLift 4099326
  have htrace : WordTrace (prefixWord ++ tailWord_4099326) baseStart_4099326 baseEnd_4099326 := by
    simpa [prefixWord, tailWord_4099326, baseEnd_4099326] using wordTrace_append hprefix tailTrace_4099326
  have hstable : (prefixWord ++ tailWord_4099326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099326).length < 2 ^ (prefixWord ++ tailWord_4099326).sum := by decide
  have hdescent : baseEnd_4099326 < baseStart_4099326 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099349 : List Nat := [1, 3, 2, 1, 2, 1, 1, 1, 2, 7, 2]
def baseStart_4099349 : Nat := 118140960795 + 4099349 * 2 ^ 59
def prefixEnd_4099349 : Nat := 4983230072969 + 3 ^ 40 * 4099349 * 2
def baseEnd_4099349 : Nat := 2104936407527987011884943

theorem tailTrace_4099349 : CollatzResearch.WordTrace tailWord_4099349 prefixEnd_4099349 2104936407527987011884943 := by
  unfold tailWord_4099349
  simp only [CollatzResearch.WordTrace]
  refine ⟨149515541225766160915461101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99677027483844107276974067 149515541225766160915461101)
  ·
    refine ⟨56068327959662310343297913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149515541225766160915461101 56068327959662310343297913)
    ·
      refine ⟨42051245969746732757473435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56068327959662310343297913 42051245969746732757473435)
      ·
        refine ⟨63076868954620099136210153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42051245969746732757473435 63076868954620099136210153)
        ·
          refine ⟨47307651715965074352157615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63076868954620099136210153 47307651715965074352157615)
          ·
            refine ⟨70961477573947611528236423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47307651715965074352157615 70961477573947611528236423)
            ·
              refine ⟨106442216360921417292354635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70961477573947611528236423 106442216360921417292354635)
              ·
                refine ⟨159663324541382125938531953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106442216360921417292354635 159663324541382125938531953)
                ·
                  refine ⟨119747493406036594453898965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159663324541382125938531953 119747493406036594453898965)
                  ·
                    refine ⟨2806581876703982682513257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 119747493406036594453898965 2806581876703982682513257)
                    ·
                      refine ⟨2104936407527987011884943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2806581876703982682513257 2104936407527987011884943)
                      ·
                        rfl

theorem cell23_4099349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 7, 2].length) (baseStart_4099349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4099349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4099349 prefixEnd_4099349 := by exact prefixLift 4099349
  have htrace : WordTrace (prefixWord ++ tailWord_4099349) baseStart_4099349 baseEnd_4099349 := by
    simpa [prefixWord, tailWord_4099349, baseEnd_4099349] using wordTrace_append hprefix tailTrace_4099349
  have hstable : (prefixWord ++ tailWord_4099349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099349).length < 2 ^ (prefixWord ++ tailWord_4099349).sum := by decide
  have hdescent : baseEnd_4099349 < baseStart_4099349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099360 : List Nat := [2, 1, 1, 5, 4, 1, 1, 2, 1, 2, 3]
def baseStart_4099360 : Nat := 118140960795 + 4099360 * 2 ^ 59
def prefixEnd_4099360 : Nat := 4983230072969 + 3 ^ 40 * 4099360 * 2
def baseEnd_4099360 : Nat := 2104942055815186468847393

theorem tailTrace_4099360 : CollatzResearch.WordTrace tailWord_4099360 prefixEnd_4099360 2104942055815186468847393 := by
  unfold tailWord_4099360
  simp only [CollatzResearch.WordTrace]
  refine ⟨74757971214363154897055767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99677294952484206529407689 74757971214363154897055767)
  ·
    refine ⟨112136956821544732345583651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74757971214363154897055767 112136956821544732345583651)
    ·
      refine ⟨168205435232317098518375477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112136956821544732345583651 168205435232317098518375477)
      ·
        refine ⟨15769259553029727986097701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 168205435232317098518375477 15769259553029727986097701)
        ·
          refine ⟨2956736166193073997393319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15769259553029727986097701 2956736166193073997393319)
          ·
            refine ⟨4435104249289610996089979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2956736166193073997393319 4435104249289610996089979)
            ·
              refine ⟨6652656373934416494134969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4435104249289610996089979 6652656373934416494134969)
              ·
                refine ⟨4989492280450812370601227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6652656373934416494134969 4989492280450812370601227)
                ·
                  refine ⟨7484238420676218555901841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4989492280450812370601227 7484238420676218555901841)
                  ·
                    refine ⟨5613178815507163916926381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7484238420676218555901841 5613178815507163916926381)
                    ·
                      refine ⟨2104942055815186468847393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5613178815507163916926381 2104942055815186468847393)
                      ·
                        rfl

theorem cell23_4099360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 2, 1, 2, 3].length) (baseStart_4099360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4099360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4099360 prefixEnd_4099360 := by exact prefixLift 4099360
  have htrace : WordTrace (prefixWord ++ tailWord_4099360) baseStart_4099360 baseEnd_4099360 := by
    simpa [prefixWord, tailWord_4099360, baseEnd_4099360] using wordTrace_append hprefix tailTrace_4099360
  have hstable : (prefixWord ++ tailWord_4099360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099360).length < 2 ^ (prefixWord ++ tailWord_4099360).sum := by decide
  have hdescent : baseEnd_4099360 < baseStart_4099360 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099372 : List Nat := [2, 2, 1, 1, 1, 3, 1, 2, 4, 6]
def baseStart_4099372 : Nat := 118140960795 + 4099372 * 2 ^ 59
def prefixEnd_4099372 : Nat := 4983230072969 + 3 ^ 40 * 4099372 * 2
def baseEnd_4099372 : Nat := 701649405861013473965779

theorem tailTrace_4099372 : CollatzResearch.WordTrace tailWord_4099372 prefixEnd_4099372 701649405861013473965779 := by
  unfold tailWord_4099372
  simp only [CollatzResearch.WordTrace]
  refine ⟨74758190052341417921774185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99677586736455223895698913 74758190052341417921774185)
  ·
    refine ⟨56068642539256063441330639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74758190052341417921774185 56068642539256063441330639)
    ·
      refine ⟨84102963808884095161995959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56068642539256063441330639 84102963808884095161995959)
      ·
        refine ⟨126154445713326142742993939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84102963808884095161995959 126154445713326142742993939)
        ·
          refine ⟨189231668569989214114490909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126154445713326142742993939 189231668569989214114490909)
          ·
            refine ⟨70961875713745955292934091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189231668569989214114490909 70961875713745955292934091)
            ·
              refine ⟨106442813570618932939401137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70961875713745955292934091 106442813570618932939401137)
              ·
                refine ⟨79832110177964199704550853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106442813570618932939401137 79832110177964199704550853)
                ·
                  refine ⟨14968520658368287444603285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79832110177964199704550853 14968520658368287444603285)
                  ·
                    refine ⟨701649405861013473965779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14968520658368287444603285 701649405861013473965779)
                    ·
                      rfl

theorem cell23_4099372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 6].length) (baseStart_4099372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4099372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4099372 prefixEnd_4099372 := by exact prefixLift 4099372
  have htrace : WordTrace (prefixWord ++ tailWord_4099372) baseStart_4099372 baseEnd_4099372 := by
    simpa [prefixWord, tailWord_4099372, baseEnd_4099372] using wordTrace_append hprefix tailTrace_4099372
  have hstable : (prefixWord ++ tailWord_4099372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099372).length < 2 ^ (prefixWord ++ tailWord_4099372).sum := by decide
  have hdescent : baseEnd_4099372 < baseStart_4099372 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099373 : List Nat := [1, 5, 3, 1, 1, 2, 1, 2, 1, 3, 3]
def baseStart_4099373 : Nat := 118140960795 + 4099373 * 2 ^ 59
def prefixEnd_4099373 : Nat := 4983230072969 + 3 ^ 40 * 4099373 * 2
def baseEnd_4099373 : Nat := 2104948731063694917984833

theorem tailTrace_4099373 : CollatzResearch.WordTrace tailWord_4099373 prefixEnd_4099373 2104948731063694917984833 := by
  unfold tailWord_4099373
  simp only [CollatzResearch.WordTrace]
  refine ⟨149516416577679213014334773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99677611051786142009556515 149516416577679213014334773)
  ·
    refine ⟨14017164054157426220093885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 149516416577679213014334773 14017164054157426220093885)
    ·
      refine ⟨5256436520309034832535207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14017164054157426220093885 5256436520309034832535207)
      ·
        refine ⟨7884654780463552248802811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5256436520309034832535207 7884654780463552248802811)
        ·
          refine ⟨11826982170695328373204217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7884654780463552248802811 11826982170695328373204217)
          ·
            refine ⟨8870236628021496279903163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11826982170695328373204217 8870236628021496279903163)
            ·
              refine ⟨13305354942032244419854745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8870236628021496279903163 13305354942032244419854745)
              ·
                refine ⟨9979016206524183314891059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13305354942032244419854745 9979016206524183314891059)
                ·
                  refine ⟨14968524309786274972336589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9979016206524183314891059 14968524309786274972336589)
                  ·
                    refine ⟨5613196616169853114626221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14968524309786274972336589 5613196616169853114626221)
                    ·
                      refine ⟨2104948731063694917984833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5613196616169853114626221 2104948731063694917984833)
                      ·
                        rfl

theorem cell23_4099373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_4099373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4099373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4099373 prefixEnd_4099373 := by exact prefixLift 4099373
  have htrace : WordTrace (prefixWord ++ tailWord_4099373) baseStart_4099373 baseEnd_4099373 := by
    simpa [prefixWord, tailWord_4099373, baseEnd_4099373] using wordTrace_append hprefix tailTrace_4099373
  have hstable : (prefixWord ++ tailWord_4099373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099373).length < 2 ^ (prefixWord ++ tailWord_4099373).sum := by decide
  have hdescent : baseEnd_4099373 < baseStart_4099373 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099396 : List Nat := [2, 3, 4, 1, 1, 1, 1, 1, 2, 3, 4]
def baseStart_4099396 : Nat := 118140960795 + 4099396 * 2 ^ 59
def prefixEnd_4099396 : Nat := 4983230072969 + 3 ^ 40 * 4099396 * 2
def baseEnd_4099396 : Nat := 2104960541118748327997227

theorem tailTrace_4099396 : CollatzResearch.WordTrace tailWord_4099396 prefixEnd_4099396 2104960541118748327997227 := by
  unfold tailWord_4099396
  simp only [CollatzResearch.WordTrace]
  refine ⟨74758627728297943971211021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99678170304397258628281361 74758627728297943971211021)
  ·
    refine ⟨28034485398111728989204133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74758627728297943971211021 28034485398111728989204133)
    ·
      refine ⟨5256466012145949185475775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28034485398111728989204133 5256466012145949185475775)
      ·
        refine ⟨7884699018218923778213663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5256466012145949185475775 7884699018218923778213663)
        ·
          refine ⟨11827048527328385667320495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7884699018218923778213663 11827048527328385667320495)
          ·
            refine ⟨17740572790992578500980743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11827048527328385667320495 17740572790992578500980743)
            ·
              refine ⟨26610859186488867751471115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17740572790992578500980743 26610859186488867751471115)
              ·
                refine ⟨39916288779733301627206673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26610859186488867751471115 39916288779733301627206673)
                ·
                  refine ⟨29937216584799976220405005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39916288779733301627206673 29937216584799976220405005)
                  ·
                    refine ⟨11226456219299991082651877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29937216584799976220405005 11226456219299991082651877)
                    ·
                      refine ⟨2104960541118748327997227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11226456219299991082651877 2104960541118748327997227)
                      ·
                        rfl

theorem cell23_4099396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_4099396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4099396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4099396 prefixEnd_4099396 := by exact prefixLift 4099396
  have htrace : WordTrace (prefixWord ++ tailWord_4099396) baseStart_4099396 baseEnd_4099396 := by
    simpa [prefixWord, tailWord_4099396, baseEnd_4099396] using wordTrace_append hprefix tailTrace_4099396
  have hstable : (prefixWord ++ tailWord_4099396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099396).length < 2 ^ (prefixWord ++ tailWord_4099396).sum := by decide
  have hdescent : baseEnd_4099396 < baseStart_4099396 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099399 : List Nat := [1, 1, 4, 1, 2, 3, 1, 1, 2, 4, 3]
def baseStart_4099399 : Nat := 118140960795 + 4099399 * 2 ^ 59
def prefixEnd_4099399 : Nat := 4983230072969 + 3 ^ 40 * 4099399 * 2
def baseEnd_4099399 : Nat := 2104962081560711816259713

theorem tailTrace_4099399 : CollatzResearch.WordTrace tailWord_4099399 prefixEnd_4099399 2104962081560711816259713 := by
  unfold tailWord_4099399
  simp only [CollatzResearch.WordTrace]
  refine ⟨149517364875585019454781251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99678243250390012969854167 149517364875585019454781251)
  ·
    refine ⟨224276047313377529182171877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149517364875585019454781251 224276047313377529182171877)
    ·
      refine ⟨42051758871258286721657227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 224276047313377529182171877 42051758871258286721657227)
      ·
        refine ⟨63077638306887430082485841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42051758871258286721657227 63077638306887430082485841)
        ·
          refine ⟨47308228730165572561864381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63077638306887430082485841 47308228730165572561864381)
          ·
            refine ⟨17740585773812089710699143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47308228730165572561864381 17740585773812089710699143)
            ·
              refine ⟨26610878660718134566048715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17740585773812089710699143 26610878660718134566048715)
              ·
                refine ⟨39916317991077201849073073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26610878660718134566048715 39916317991077201849073073)
                ·
                  refine ⟨29937238493307901386804805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39916317991077201849073073 29937238493307901386804805)
                  ·
                    refine ⟨5613232217495231510025901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29937238493307901386804805 5613232217495231510025901)
                    ·
                      refine ⟨2104962081560711816259713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5613232217495231510025901 2104962081560711816259713)
                      ·
                        rfl

theorem cell23_4099399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 4, 3].length) (baseStart_4099399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4099399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4099399 prefixEnd_4099399 := by exact prefixLift 4099399
  have htrace : WordTrace (prefixWord ++ tailWord_4099399) baseStart_4099399 baseEnd_4099399 := by
    simpa [prefixWord, tailWord_4099399, baseEnd_4099399] using wordTrace_append hprefix tailTrace_4099399
  have hstable : (prefixWord ++ tailWord_4099399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099399).length < 2 ^ (prefixWord ++ tailWord_4099399).sum := by decide
  have hdescent : baseEnd_4099399 < baseStart_4099399 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099402 : List Nat := [3, 1, 2, 1, 1, 1, 1, 2, 11]
def baseStart_4099402 : Nat := 118140960795 + 4099402 * 2 ^ 59
def prefixEnd_4099402 : Nat := 4983230072969 + 3 ^ 40 * 4099402 * 2
def baseEnd_4099402 : Nat := 233884846889186144946911

theorem tailTrace_4099402 : CollatzResearch.WordTrace tailWord_4099402 prefixEnd_4099402 233884846889186144946911 := by
  unfold tailWord_4099402
  simp only [CollatzResearch.WordTrace]
  refine ⟨37379368573643537741785115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99678316196382767311426973 37379368573643537741785115)
  ·
    refine ⟨56069052860465306612677673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37379368573643537741785115 56069052860465306612677673)
    ·
      refine ⟨42051789645348979959508255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56069052860465306612677673 42051789645348979959508255)
      ·
        refine ⟨63077684468023469939262383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42051789645348979959508255 63077684468023469939262383)
        ·
          refine ⟨94616526702035204908893575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63077684468023469939262383 94616526702035204908893575)
          ·
            refine ⟨141924790053052807363340363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94616526702035204908893575 141924790053052807363340363)
            ·
              refine ⟨212887185079579211045010545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141924790053052807363340363 212887185079579211045010545)
              ·
                refine ⟨159665388809684408283757909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 212887185079579211045010545 159665388809684408283757909)
                ·
                  refine ⟨233884846889186144946911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 159665388809684408283757909 233884846889186144946911)
                  ·
                    rfl

theorem cell23_4099402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 11].length) (baseStart_4099402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4099402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4099402 prefixEnd_4099402 := by exact prefixLift 4099402
  have htrace : WordTrace (prefixWord ++ tailWord_4099402) baseStart_4099402 baseEnd_4099402 := by
    simpa [prefixWord, tailWord_4099402, baseEnd_4099402] using wordTrace_append hprefix tailTrace_4099402
  have hstable : (prefixWord ++ tailWord_4099402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099402).length < 2 ^ (prefixWord ++ tailWord_4099402).sum := by decide
  have hdescent : baseEnd_4099402 < baseStart_4099402 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099409 : List Nat := [1, 2, 2, 1, 4, 1, 3, 1, 2, 2, 4]
def baseStart_4099409 : Nat := 118140960795 + 4099409 * 2 ^ 59
def prefixEnd_4099409 : Nat := 4983230072969 + 3 ^ 40 * 4099409 * 2
def baseEnd_4099409 : Nat := 2104967216367256777134667

theorem tailTrace_4099409 : CollatzResearch.WordTrace tailWord_4099409 prefixEnd_4099409 2104967216367256777134667 := by
  unfold tailWord_4099409
  simp only [CollatzResearch.WordTrace]
  refine ⟨149517729605548791162645281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99678486403699194108430187 149517729605548791162645281)
  ·
    refine ⟨112138297204161593371983961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149517729605548791162645281 112138297204161593371983961)
    ·
      refine ⟨84103722903121195028987971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112138297204161593371983961 84103722903121195028987971)
      ·
        refine ⟨126155584354681792543481957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84103722903121195028987971 126155584354681792543481957)
        ·
          refine ⟨23654172066502836101902867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126155584354681792543481957 23654172066502836101902867)
          ·
            refine ⟨35481258099754254152854301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23654172066502836101902867 35481258099754254152854301)
            ·
              refine ⟨13305471787407845307320363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35481258099754254152854301 13305471787407845307320363)
              ·
                refine ⟨19958207681111767960980545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13305471787407845307320363 19958207681111767960980545)
                ·
                  refine ⟨14968655760833825970735409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19958207681111767960980545 14968655760833825970735409)
                  ·
                    refine ⟨11226491820625369478051557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14968655760833825970735409 11226491820625369478051557)
                    ·
                      refine ⟨2104967216367256777134667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11226491820625369478051557 2104967216367256777134667)
                      ·
                        rfl

theorem cell23_4099409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 2, 2, 4].length) (baseStart_4099409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4099409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4099409 prefixEnd_4099409 := by exact prefixLift 4099409
  have htrace : WordTrace (prefixWord ++ tailWord_4099409) baseStart_4099409 baseEnd_4099409 := by
    simpa [prefixWord, tailWord_4099409, baseEnd_4099409] using wordTrace_append hprefix tailTrace_4099409
  have hstable : (prefixWord ++ tailWord_4099409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099409).length < 2 ^ (prefixWord ++ tailWord_4099409).sum := by decide
  have hdescent : baseEnd_4099409 < baseStart_4099409 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099413 : List Nat := [1, 3, 2, 2, 3, 2, 2, 1, 1, 4, 2]
def baseStart_4099413 : Nat := 118140960795 + 4099413 * 2 ^ 59
def prefixEnd_4099413 : Nat := 4983230072969 + 3 ^ 40 * 4099413 * 2
def baseEnd_4099413 : Nat := 2104969270289874761484649

theorem tailTrace_4099413 : CollatzResearch.WordTrace tailWord_4099413 prefixEnd_4099413 2104969270289874761484649 := by
  unfold tailWord_4099413
  simp only [CollatzResearch.WordTrace]
  refine ⟨149517875497534299845790893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99678583665022866563860595 149517875497534299845790893)
  ·
    refine ⟨56069203311575362442171585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149517875497534299845790893 56069203311575362442171585)
    ·
      refine ⟨42051902483681521831628689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56069203311575362442171585 42051902483681521831628689)
      ·
        refine ⟨31538926862761141373721517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42051902483681521831628689 31538926862761141373721517)
        ·
          refine ⟨11827097573535428015145569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31538926862761141373721517 11827097573535428015145569)
          ·
            refine ⟨8870323180151571011359177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11827097573535428015145569 8870323180151571011359177)
            ·
              refine ⟨6652742385113678258519383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8870323180151571011359177 6652742385113678258519383)
              ·
                refine ⟨9979113577670517387779075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6652742385113678258519383 9979113577670517387779075)
                ·
                  refine ⟨14968670366505776081668613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9979113577670517387779075 14968670366505776081668613)
                  ·
                    refine ⟨2806625693719833015312865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14968670366505776081668613 2806625693719833015312865)
                    ·
                      refine ⟨2104969270289874761484649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2806625693719833015312865 2104969270289874761484649)
                      ·
                        rfl

theorem cell23_4099413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 1, 1, 4, 2].length) (baseStart_4099413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4099413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4099413 prefixEnd_4099413 := by exact prefixLift 4099413
  have htrace : WordTrace (prefixWord ++ tailWord_4099413) baseStart_4099413 baseEnd_4099413 := by
    simpa [prefixWord, tailWord_4099413, baseEnd_4099413] using wordTrace_append hprefix tailTrace_4099413
  have hstable : (prefixWord ++ tailWord_4099413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099413).length < 2 ^ (prefixWord ++ tailWord_4099413).sum := by decide
  have hdescent : baseEnd_4099413 < baseStart_4099413 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099429 : List Nat := [1, 3, 1, 3, 1, 2, 1, 2, 1, 5, 3]
def baseStart_4099429 : Nat := 118140960795 + 4099429 * 2 ^ 59
def prefixEnd_4099429 : Nat := 4983230072969 + 3 ^ 40 * 4099429 * 2
def baseEnd_4099429 : Nat := 2104977485980346698884575

theorem tailTrace_4099429 : CollatzResearch.WordTrace tailWord_4099429 prefixEnd_4099429 2104977485980346698884575 := by
  unfold tailWord_4099429
  simp only [CollatzResearch.WordTrace]
  refine ⟨149518459065476334578373341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99678972710317556385582227 149518459065476334578373341)
  ·
    refine ⟨56069422149553625466890003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149518459065476334578373341 56069422149553625466890003)
    ·
      refine ⟨84104133224330438200335005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56069422149553625466890003 84104133224330438200335005)
      ·
        refine ⟨31539049959123914325125627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84104133224330438200335005 31539049959123914325125627)
        ·
          refine ⟨47308574938685871487688441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31539049959123914325125627 47308574938685871487688441)
          ·
            refine ⟨35481431204014403615766331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47308574938685871487688441 35481431204014403615766331)
            ·
              refine ⟨53222146806021605423649497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35481431204014403615766331 53222146806021605423649497)
              ·
                refine ⟨39916610104516204067737123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53222146806021605423649497 39916610104516204067737123)
                ·
                  refine ⟨59874915156774306101605685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39916610104516204067737123 59874915156774306101605685)
                  ·
                    refine ⟨5613273295947591197025533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59874915156774306101605685 5613273295947591197025533)
                    ·
                      refine ⟨2104977485980346698884575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5613273295947591197025533 2104977485980346698884575)
                      ·
                        rfl

theorem cell23_4099429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 5, 3].length) (baseStart_4099429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4099429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4099429 prefixEnd_4099429 := by exact prefixLift 4099429
  have htrace : WordTrace (prefixWord ++ tailWord_4099429) baseStart_4099429 baseEnd_4099429 := by
    simpa [prefixWord, tailWord_4099429, baseEnd_4099429] using wordTrace_append hprefix tailTrace_4099429
  have hstable : (prefixWord ++ tailWord_4099429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099429).length < 2 ^ (prefixWord ++ tailWord_4099429).sum := by decide
  have hdescent : baseEnd_4099429 < baseStart_4099429 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099434 : List Nat := [3, 1, 3, 3, 3, 1, 2, 1, 1, 3, 2]
def baseStart_4099434 : Nat := 118140960795 + 4099434 * 2 ^ 59
def prefixEnd_4099434 : Nat := 4983230072969 + 3 ^ 40 * 4099434 * 2
def baseEnd_4099434 : Nat := 2104980053383619179322053

theorem tailTrace_4099434 : CollatzResearch.WordTrace tailWord_4099434 prefixEnd_4099434 2104980053383619179322053 := by
  unfold tailWord_4099434
  simp only [CollatzResearch.WordTrace]
  refine ⟨37379660357614555108076339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99679094286972146954870237 37379660357614555108076339)
  ·
    refine ⟨56069490536421832662114509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37379660357614555108076339 56069490536421832662114509)
    ·
      refine ⟨21026058951158187248292941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56069490536421832662114509 21026058951158187248292941)
      ·
        refine ⟨7884772106684320218109853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21026058951158187248292941 7884772106684320218109853)
        ·
          refine ⟨2956789540006620081791195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7884772106684320218109853 2956789540006620081791195)
          ·
            refine ⟨4435184310009930122686793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2956789540006620081791195 4435184310009930122686793)
            ·
              refine ⟨3326388232507447592015095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4435184310009930122686793 3326388232507447592015095)
              ·
                refine ⟨4989582348761171388022643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3326388232507447592015095 4989582348761171388022643)
                ·
                  refine ⟨7484373523141757082033965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4989582348761171388022643 7484373523141757082033965)
                  ·
                    refine ⟨2806640071178158905762737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7484373523141757082033965 2806640071178158905762737)
                    ·
                      refine ⟨2104980053383619179322053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2806640071178158905762737 2104980053383619179322053)
                      ·
                        rfl

theorem cell23_4099434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_4099434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4099434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4099434 prefixEnd_4099434 := by exact prefixLift 4099434
  have htrace : WordTrace (prefixWord ++ tailWord_4099434) baseStart_4099434 baseEnd_4099434 := by
    simpa [prefixWord, tailWord_4099434, baseEnd_4099434] using wordTrace_append hprefix tailTrace_4099434
  have hstable : (prefixWord ++ tailWord_4099434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099434).length < 2 ^ (prefixWord ++ tailWord_4099434).sum := by decide
  have hdescent : baseEnd_4099434 < baseStart_4099434 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099436 : List Nat := [2, 2, 1, 1, 5, 1, 1, 5, 5]
def baseStart_4099436 : Nat := 118140960795 + 4099436 * 2 ^ 59
def prefixEnd_4099436 : Nat := 4983230072969 + 3 ^ 40 * 4099436 * 2
def baseEnd_4099436 : Nat := 233886786704992019055227

theorem tailTrace_4099436 : CollatzResearch.WordTrace tailWord_4099436 prefixEnd_4099436 233886786704992019055227 := by
  unfold tailWord_4099436
  simp only [CollatzResearch.WordTrace]
  refine ⟨74759357188225487386939081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99679142917633983182585441 74759357188225487386939081)
  ·
    refine ⟨56069517891169115540204311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74759357188225487386939081 56069517891169115540204311)
    ·
      refine ⟨84104276836753673310306467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56069517891169115540204311 84104276836753673310306467)
      ·
        refine ⟨126156415255130509965459701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84104276836753673310306467 126156415255130509965459701)
        ·
          refine ⟨11827163930168485309261847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 126156415255130509965459701 11827163930168485309261847)
          ·
            refine ⟨17740745895252727963892771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11827163930168485309261847 17740745895252727963892771)
            ·
              refine ⟨26611118842879091945839157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17740745895252727963892771 26611118842879091945839157)
              ·
                refine ⟨2494792391519914869922421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26611118842879091945839157 2494792391519914869922421)
                ·
                  refine ⟨233886786704992019055227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2494792391519914869922421 233886786704992019055227)
                  ·
                    rfl

theorem cell23_4099436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 5, 5].length) (baseStart_4099436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4099436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4099436 prefixEnd_4099436 := by exact prefixLift 4099436
  have htrace : WordTrace (prefixWord ++ tailWord_4099436) baseStart_4099436 baseEnd_4099436 := by
    simpa [prefixWord, tailWord_4099436, baseEnd_4099436] using wordTrace_append hprefix tailTrace_4099436
  have hstable : (prefixWord ++ tailWord_4099436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099436).length < 2 ^ (prefixWord ++ tailWord_4099436).sum := by decide
  have hdescent : baseEnd_4099436 < baseStart_4099436 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099449 : List Nat := [1, 2, 1, 3, 2, 1, 2, 4, 2, 5]
def baseStart_4099449 : Nat := 118140960795 + 4099449 * 2 ^ 59
def prefixEnd_4099449 : Nat := 4983230072969 + 3 ^ 40 * 4099449 * 2
def baseEnd_4099449 : Nat := 701662585197812206878161

theorem tailTrace_4099449 : CollatzResearch.WordTrace tailWord_4099449 prefixEnd_4099449 701662585197812206878161 := by
  unfold tailWord_4099449
  simp only [CollatzResearch.WordTrace]
  refine ⟨149519188525403877994101401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99679459016935918662734267 149519188525403877994101401)
  ·
    refine ⟨112139391394052908495576051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149519188525403877994101401 112139391394052908495576051)
    ·
      refine ⟨168209087091079362743364077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112139391394052908495576051 168209087091079362743364077)
      ·
        refine ⟨63078407659154761028761529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168209087091079362743364077 63078407659154761028761529)
        ·
          refine ⟨47308805744366070771571147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63078407659154761028761529 47308805744366070771571147)
          ·
            refine ⟨70963208616549106157356721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47308805744366070771571147 70963208616549106157356721)
            ·
              refine ⟨53222406462411829618017541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70963208616549106157356721 53222406462411829618017541)
              ·
                refine ⟨9979201211702218053378289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53222406462411829618017541 9979201211702218053378289)
                ·
                  refine ⟨7484400908776663540033717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9979201211702218053378289 7484400908776663540033717)
                  ·
                    refine ⟨701662585197812206878161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7484400908776663540033717 701662585197812206878161)
                    ·
                      rfl

theorem cell23_4099449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 4, 2, 5].length) (baseStart_4099449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4099449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4099449 prefixEnd_4099449 := by exact prefixLift 4099449
  have htrace : WordTrace (prefixWord ++ tailWord_4099449) baseStart_4099449 baseEnd_4099449 := by
    simpa [prefixWord, tailWord_4099449, baseEnd_4099449] using wordTrace_append hprefix tailTrace_4099449
  have hstable : (prefixWord ++ tailWord_4099449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099449).length < 2 ^ (prefixWord ++ tailWord_4099449).sum := by decide
  have hdescent : baseEnd_4099449 < baseStart_4099449 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099540 : List Nat := [2, 4, 1, 2, 3, 1, 2, 1, 2, 2, 3]
def baseStart_4099540 : Nat := 118140960795 + 4099540 * 2 ^ 59
def prefixEnd_4099540 : Nat := 4983230072969 + 3 ^ 40 * 4099540 * 2
def baseEnd_4099540 : Nat := 2105034482332995764596565

theorem tailTrace_4099540 : CollatzResearch.WordTrace tailWord_4099540 prefixEnd_4099540 2105034482332995764596565 := by
  unfold tailWord_4099540
  simp only [CollatzResearch.WordTrace]
  refine ⟨74761253784037100267832037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99681671712049467023776049 74761253784037100267832037)
  ·
    refine ⟨14017735084506956300218507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74761253784037100267832037 14017735084506956300218507)
    ·
      refine ⟨21026602626760434450327761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14017735084506956300218507 21026602626760434450327761)
      ·
        refine ⟨15769951970070325837745821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21026602626760434450327761 15769951970070325837745821)
        ·
          refine ⟨5913731988776372189154683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15769951970070325837745821 5913731988776372189154683)
          ·
            refine ⟨8870597983164558283732025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5913731988776372189154683 8870597983164558283732025)
            ·
              refine ⟨6652948487373418712799019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8870597983164558283732025 6652948487373418712799019)
              ·
                refine ⟨9979422731060128069198529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6652948487373418712799019 9979422731060128069198529)
                ·
                  refine ⟨7484567048295096051898897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9979422731060128069198529 7484567048295096051898897)
                  ·
                    refine ⟨5613425286221322038924173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7484567048295096051898897 5613425286221322038924173)
                    ·
                      refine ⟨2105034482332995764596565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5613425286221322038924173 2105034482332995764596565)
                      ·
                        rfl

theorem cell23_4099540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_4099540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4099540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4099540 prefixEnd_4099540 := by exact prefixLift 4099540
  have htrace : WordTrace (prefixWord ++ tailWord_4099540) baseStart_4099540 baseEnd_4099540 := by
    simpa [prefixWord, tailWord_4099540, baseEnd_4099540] using wordTrace_append hprefix tailTrace_4099540
  have hstable : (prefixWord ++ tailWord_4099540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099540).length < 2 ^ (prefixWord ++ tailWord_4099540).sum := by decide
  have hdescent : baseEnd_4099540 < baseStart_4099540 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099556 : List Nat := [2, 3, 1, 1, 1, 1, 1, 7, 1, 5]
def baseStart_4099556 : Nat := 118140960795 + 4099556 * 2 ^ 59
def prefixEnd_4099556 : Nat := 4983230072969 + 3 ^ 40 * 4099556 * 2
def baseEnd_4099556 : Nat := 701680899341155900665497

theorem tailTrace_4099556 : CollatzResearch.WordTrace tailWord_4099556 prefixEnd_4099556 701680899341155900665497 := by
  unfold tailWord_4099556
  simp only [CollatzResearch.WordTrace]
  refine ⟨74761545568008117634123261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99682060757344156845497681 74761545568008117634123261)
  ·
    refine ⟨28035579588003044112796223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74761545568008117634123261 28035579588003044112796223)
    ·
      refine ⟨42053369382004566169194335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28035579588003044112796223 42053369382004566169194335)
      ·
        refine ⟨63080054073006849253791503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42053369382004566169194335 63080054073006849253791503)
        ·
          refine ⟨94620081109510273880687255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63080054073006849253791503 94620081109510273880687255)
          ·
            refine ⟨141930121664265410821030883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94620081109510273880687255 141930121664265410821030883)
            ·
              refine ⟨212895182496398116231546325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141930121664265410821030883 212895182496398116231546325)
              ·
                refine ⟨4989730839759330849176867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 212895182496398116231546325 4989730839759330849176867)
                ·
                  refine ⟨7484596259638996273765301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4989730839759330849176867 7484596259638996273765301)
                  ·
                    refine ⟨701680899341155900665497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7484596259638996273765301 701680899341155900665497)
                    ·
                      rfl

theorem cell23_4099556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 7, 1, 5].length) (baseStart_4099556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4099556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4099556 prefixEnd_4099556 := by exact prefixLift 4099556
  have htrace : WordTrace (prefixWord ++ tailWord_4099556) baseStart_4099556 baseEnd_4099556 := by
    simpa [prefixWord, tailWord_4099556, baseEnd_4099556] using wordTrace_append hprefix tailTrace_4099556
  have hstable : (prefixWord ++ tailWord_4099556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099556).length < 2 ^ (prefixWord ++ tailWord_4099556).sum := by decide
  have hdescent : baseEnd_4099556 < baseStart_4099556 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099573 : List Nat := [1, 3, 5, 1, 1, 1, 1, 2, 3, 5]
def baseStart_4099573 : Nat := 118140960795 + 4099573 * 2 ^ 59
def prefixEnd_4099573 : Nat := 4983230072969 + 3 ^ 40 * 4099573 * 2
def baseEnd_4099573 : Nat := 701683809064864711827971

theorem tailTrace_4099573 : CollatzResearch.WordTrace tailWord_4099573 prefixEnd_4099573 701683809064864711827971 := by
  unfold tailWord_4099573
  simp only [CollatzResearch.WordTrace]
  refine ⟨149523711176954647171615373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99682474117969764781076915 149523711176954647171615373)
  ·
    refine ⟨56071391691357992689355765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149523711176954647171615373 56071391691357992689355765)
    ·
      refine ⟨5256692971064811814627103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56071391691357992689355765 5256692971064811814627103)
      ·
        refine ⟨7885039456597217721940655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5256692971064811814627103 7885039456597217721940655)
        ·
          refine ⟨11827559184895826582910983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7885039456597217721940655 11827559184895826582910983)
          ·
            refine ⟨17741338777343739874366475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11827559184895826582910983 17741338777343739874366475)
            ·
              refine ⟨26612008166015609811549713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17741338777343739874366475 26612008166015609811549713)
              ·
                refine ⟨19959006124511707358662285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26612008166015609811549713 19959006124511707358662285)
                ·
                  refine ⟨7484627296691890259498357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19959006124511707358662285 7484627296691890259498357)
                  ·
                    refine ⟨701683809064864711827971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7484627296691890259498357 701683809064864711827971)
                    ·
                      rfl

theorem cell23_4099573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_4099573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4099573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4099573 prefixEnd_4099573 := by exact prefixLift 4099573
  have htrace : WordTrace (prefixWord ++ tailWord_4099573) baseStart_4099573 baseEnd_4099573 := by
    simpa [prefixWord, tailWord_4099573, baseEnd_4099573] using wordTrace_append hprefix tailTrace_4099573
  have hstable : (prefixWord ++ tailWord_4099573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099573).length < 2 ^ (prefixWord ++ tailWord_4099573).sum := by decide
  have hdescent : baseEnd_4099573 < baseStart_4099573 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099576 : List Nat := [2, 1, 2, 1, 1, 5, 1, 2, 3, 1, 4]
def baseStart_4099576 : Nat := 118140960795 + 4099576 * 2 ^ 59
def prefixEnd_4099576 : Nat := 4983230072969 + 3 ^ 40 * 4099576 * 2
def baseEnd_4099576 : Nat := 2105052967636557623746399

theorem tailTrace_4099576 : CollatzResearch.WordTrace tailWord_4099576 prefixEnd_4099576 2105052967636557623746399 := by
  unfold tailWord_4099576
  simp only [CollatzResearch.WordTrace]
  refine ⟨74761910297971889341987291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99682547063962519122649721 74761910297971889341987291)
  ·
    refine ⟨112142865446957834012980937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74761910297971889341987291 112142865446957834012980937)
    ·
      refine ⟨84107149085218375509735703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112142865446957834012980937 84107149085218375509735703)
      ·
        refine ⟨126160723627827563264603555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84107149085218375509735703 126160723627827563264603555)
        ·
          refine ⟨189241085441741344896905333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126160723627827563264603555 189241085441741344896905333)
          ·
            refine ⟨17741351760163251084084875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 189241085441741344896905333 17741351760163251084084875)
            ·
              refine ⟨26612027640244876626127313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17741351760163251084084875 26612027640244876626127313)
              ·
                refine ⟨19959020730183657469595485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26612027640244876626127313 19959020730183657469595485)
                ·
                  refine ⟨7484632773818871551098307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19959020730183657469595485 7484632773818871551098307)
                  ·
                    refine ⟨11226949160728307326647461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7484632773818871551098307 11226949160728307326647461)
                    ·
                      refine ⟨2105052967636557623746399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11226949160728307326647461 2105052967636557623746399)
                      ·
                        rfl

theorem cell23_4099576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 3, 1, 4].length) (baseStart_4099576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4099576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4099576 prefixEnd_4099576 := by exact prefixLift 4099576
  have htrace : WordTrace (prefixWord ++ tailWord_4099576) baseStart_4099576 baseEnd_4099576 := by
    simpa [prefixWord, tailWord_4099576, baseEnd_4099576] using wordTrace_append hprefix tailTrace_4099576
  have hstable : (prefixWord ++ tailWord_4099576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099576).length < 2 ^ (prefixWord ++ tailWord_4099576).sum := by decide
  have hdescent : baseEnd_4099576 < baseStart_4099576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099616 : List Nat := [2, 1, 1, 6, 1, 2, 10]
def baseStart_4099616 : Nat := 118140960795 + 4099616 * 2 ^ 59
def prefixEnd_4099616 : Nat := 4983230072969 + 3 ^ 40 * 4099616 * 2
def baseEnd_4099616 : Nat := 25988561813120215645015

theorem tailTrace_4099616 : CollatzResearch.WordTrace tailWord_4099616 prefixEnd_4099616 25988561813120215645015 := by
  unfold tailWord_4099616
  simp only [CollatzResearch.WordTrace]
  refine ⟨74762639757899432757715351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99683519677199243676953801 74762639757899432757715351)
  ·
    refine ⟨112143959636849149136573027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74762639757899432757715351 112143959636849149136573027)
    ·
      refine ⟨168215939455273723704859541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112143959636849149136573027 168215939455273723704859541)
      ·
        refine ⟨7885122161965955798665291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 168215939455273723704859541 7885122161965955798665291)
        ·
          refine ⟨11827683242948933697997937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7885122161965955798665291 11827683242948933697997937)
          ·
            refine ⟨8870762432211700273498453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11827683242948933697997937 8870762432211700273498453)
            ·
              refine ⟨25988561813120215645015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8870762432211700273498453 25988561813120215645015)
              ·
                rfl

theorem cell23_4099616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 10].length) (baseStart_4099616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4099616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4099616 prefixEnd_4099616 := by exact prefixLift 4099616
  have htrace : WordTrace (prefixWord ++ tailWord_4099616) baseStart_4099616 baseEnd_4099616 := by
    simpa [prefixWord, tailWord_4099616, baseEnd_4099616] using wordTrace_append hprefix tailTrace_4099616
  have hstable : (prefixWord ++ tailWord_4099616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099616).length < 2 ^ (prefixWord ++ tailWord_4099616).sum := by decide
  have hdescent : baseEnd_4099616 < baseStart_4099616 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099723 : List Nat := [1, 1, 1, 1, 4, 1, 4, 5, 5]
def baseStart_4099723 : Nat := 118140960795 + 4099723 * 2 ^ 59
def prefixEnd_4099723 : Nat := 4983230072969 + 3 ^ 40 * 4099723 * 2
def baseEnd_4099723 : Nat := 233903161032529838734247

theorem tailTrace_4099723 : CollatzResearch.WordTrace tailWord_4099723 prefixEnd_4099723 233903161032529838734247 := by
  unfold tailWord_4099723
  simp only [CollatzResearch.WordTrace]
  refine ⟨149529182126411222789575823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99686121417607481859717215 149529182126411222789575823)
  ·
    refine ⟨224293773189616834184363735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149529182126411222789575823 224293773189616834184363735)
    ·
      refine ⟨336440659784425251276545603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224293773189616834184363735 336440659784425251276545603)
      ·
        refine ⟨504660989676637876914818405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336440659784425251276545603 504660989676637876914818405)
        ·
          refine ⟨94623935564369601921528451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 504660989676637876914818405 94623935564369601921528451)
          ·
            refine ⟨141935903346554402882292677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94623935564369601921528451 141935903346554402882292677)
            ·
              refine ⟨26612981877478950540429877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141935903346554402882292677 26612981877478950540429877)
              ·
                refine ⟨2494967051013651613165301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26612981877478950540429877 2494967051013651613165301)
                ·
                  refine ⟨233903161032529838734247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2494967051013651613165301 233903161032529838734247)
                  ·
                    rfl

theorem cell23_4099723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 5, 5].length) (baseStart_4099723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4099723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4099723 prefixEnd_4099723 := by exact prefixLift 4099723
  have htrace : WordTrace (prefixWord ++ tailWord_4099723) baseStart_4099723 baseEnd_4099723 := by
    simpa [prefixWord, tailWord_4099723, baseEnd_4099723] using wordTrace_append hprefix tailTrace_4099723
  have hstable : (prefixWord ++ tailWord_4099723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099723).length < 2 ^ (prefixWord ++ tailWord_4099723).sum := by decide
  have hdescent : baseEnd_4099723 < baseStart_4099723 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099770 : List Nat := [3, 1, 1, 1, 2, 6, 1, 1, 2, 5]
def baseStart_4099770 : Nat := 118140960795 + 4099770 * 2 ^ 59
def prefixEnd_4099770 : Nat := 4983230072969 + 3 ^ 40 * 4099770 * 2
def baseEnd_4099770 : Nat := 701717527627843288240169

theorem tailTrace_4099770 : CollatzResearch.WordTrace tailWord_4099770 prefixEnd_4099770 701717527627843288240169 := by
  unfold tailWord_4099770
  simp only [CollatzResearch.WordTrace]
  refine ⟨37382724089310237454134191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99687264238160633211024509 37382724089310237454134191)
  ·
    refine ⟨56074086133965356181201287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37382724089310237454134191 56074086133965356181201287)
    ·
      refine ⟨84111129200948034271801931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56074086133965356181201287 84111129200948034271801931)
      ·
        refine ⟨126166693801422051407702897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84111129200948034271801931 126166693801422051407702897)
        ·
          refine ⟨94625020351066538555777173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126166693801422051407702897 94625020351066538555777173)
          ·
            refine ⟨4435547828956243994802055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 94625020351066538555777173 4435547828956243994802055)
            ·
              refine ⟨6653321743434365992203083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4435547828956243994802055 6653321743434365992203083)
              ·
                refine ⟨9979982615151548988304625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6653321743434365992203083 9979982615151548988304625)
                ·
                  refine ⟨7484986961363661741228469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9979982615151548988304625 7484986961363661741228469)
                  ·
                    refine ⟨701717527627843288240169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7484986961363661741228469 701717527627843288240169)
                    ·
                      rfl

theorem cell23_4099770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 1, 2, 5].length) (baseStart_4099770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4099770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4099770 prefixEnd_4099770 := by exact prefixLift 4099770
  have htrace : WordTrace (prefixWord ++ tailWord_4099770) baseStart_4099770 baseEnd_4099770 := by
    simpa [prefixWord, tailWord_4099770, baseEnd_4099770] using wordTrace_append hprefix tailTrace_4099770
  have hstable : (prefixWord ++ tailWord_4099770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099770).length < 2 ^ (prefixWord ++ tailWord_4099770).sum := by decide
  have hdescent : baseEnd_4099770 < baseStart_4099770 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099773 : List Nat := [1, 4, 1, 2, 1, 2, 3, 1, 1, 3, 4]
def baseStart_4099773 : Nat := 118140960795 + 4099773 * 2 ^ 59
def prefixEnd_4099773 : Nat := 4983230072969 + 3 ^ 40 * 4099773 * 2
def baseEnd_4099773 : Nat := 2105154123325493352982993

theorem tailTrace_4099773 : CollatzResearch.WordTrace tailWord_4099773 prefixEnd_4099773 2105154123325493352982993 := by
  unfold tailWord_4099773
  simp only [CollatzResearch.WordTrace]
  refine ⟨149531005776230081328895973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99687337184153387552597315 149531005776230081328895973)
  ·
    refine ⟨28037063583043140249167995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149531005776230081328895973 28037063583043140249167995)
    ·
      refine ⟨42055595374564710373751993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28037063583043140249167995 42055595374564710373751993)
      ·
        refine ⟨31541696530923532780313995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42055595374564710373751993 31541696530923532780313995)
        ·
          refine ⟨47312544796385299170470993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31541696530923532780313995 47312544796385299170470993)
          ·
            refine ⟨35484408597288974377853245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47312544796385299170470993 35484408597288974377853245)
            ·
              refine ⟨13306653223983365391694967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35484408597288974377853245 13306653223983365391694967)
              ·
                refine ⟨19959979835975048087542451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13306653223983365391694967 19959979835975048087542451)
                ·
                  refine ⟨29939969753962572131313677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19959979835975048087542451 29939969753962572131313677)
                  ·
                    refine ⟨11227488657735964549242629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29939969753962572131313677 11227488657735964549242629)
                    ·
                      refine ⟨2105154123325493352982993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11227488657735964549242629 2105154123325493352982993)
                      ·
                        rfl

theorem cell23_4099773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_4099773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4099773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4099773 prefixEnd_4099773 := by exact prefixLift 4099773
  have htrace : WordTrace (prefixWord ++ tailWord_4099773) baseStart_4099773 baseEnd_4099773 := by
    simpa [prefixWord, tailWord_4099773, baseEnd_4099773] using wordTrace_append hprefix tailTrace_4099773
  have hstable : (prefixWord ++ tailWord_4099773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099773).length < 2 ^ (prefixWord ++ tailWord_4099773).sum := by decide
  have hdescent : baseEnd_4099773 < baseStart_4099773 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099783 : List Nat := [1, 1, 4, 1, 1, 1, 3, 2, 5, 4]
def baseStart_4099783 : Nat := 118140960795 + 4099783 * 2 ^ 59
def prefixEnd_4099783 : Nat := 4983230072969 + 3 ^ 40 * 4099783 * 2
def baseEnd_4099783 : Nat := 701719752710679437952649

theorem tailTrace_4099783 : CollatzResearch.WordTrace tailWord_4099783 prefixEnd_4099783 701719752710679437952649 := by
  unfold tailWord_4099783
  simp only [CollatzResearch.WordTrace]
  refine ⟨149531370506193853036760003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99687580337462568691173335 149531370506193853036760003)
  ·
    refine ⟨224297055759290779555140005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149531370506193853036760003 224297055759290779555140005)
    ·
      refine ⟨42055697954867021166588751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 224297055759290779555140005 42055697954867021166588751)
      ·
        refine ⟨63083546932300531749883127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42055697954867021166588751 63083546932300531749883127)
        ·
          refine ⟨94625320398450797624824691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63083546932300531749883127 94625320398450797624824691)
          ·
            refine ⟨141937980597676196437237037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94625320398450797624824691 141937980597676196437237037)
            ·
              refine ⟨53226742724128573663963889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141937980597676196437237037 53226742724128573663963889)
              ·
                refine ⟨39920057043096430247972917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53226742724128573663963889 39920057043096430247972917)
                ·
                  refine ⟨3742505347790290335747461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39920057043096430247972917 3742505347790290335747461)
                  ·
                    refine ⟨701719752710679437952649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3742505347790290335747461 701719752710679437952649)
                    ·
                      rfl

theorem cell23_4099783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 5, 4].length) (baseStart_4099783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4099783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4099783 prefixEnd_4099783 := by exact prefixLift 4099783
  have htrace : WordTrace (prefixWord ++ tailWord_4099783) baseStart_4099783 baseEnd_4099783 := by
    simpa [prefixWord, tailWord_4099783, baseEnd_4099783] using wordTrace_append hprefix tailTrace_4099783
  have hstable : (prefixWord ++ tailWord_4099783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099783).length < 2 ^ (prefixWord ++ tailWord_4099783).sum := by decide
  have hdescent : baseEnd_4099783 < baseStart_4099783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099790 : List Nat := [4, 1, 1, 1, 3, 1, 1, 1, 4, 4, 2]
def baseStart_4099790 : Nat := 118140960795 + 4099790 * 2 ^ 59
def prefixEnd_4099790 : Nat := 4983230072969 + 3 ^ 40 * 4099790 * 2
def baseEnd_4099790 : Nat := 2105162852496619786470415

theorem tailTrace_4099790 : CollatzResearch.WordTrace tailWord_4099790 prefixEnd_4099790 2105162852496619786470415 := by
  unfold tailWord_4099790
  simp only [CollatzResearch.WordTrace]
  refine ⟨18691453227146061654033103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99687750544778995488176549 18691453227146061654033103)
  ·
    refine ⟨28037179840719092481049655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18691453227146061654033103 28037179840719092481049655)
    ·
      refine ⟨42055769761078638721574483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28037179840719092481049655 42055769761078638721574483)
      ·
        refine ⟨63083654641617958082361725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42055769761078638721574483 63083654641617958082361725)
        ·
          refine ⟨23656370490606734280885647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63083654641617958082361725 23656370490606734280885647)
          ·
            refine ⟨35484555735910101421328471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23656370490606734280885647 35484555735910101421328471)
            ·
              refine ⟨53226833603865152131992707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35484555735910101421328471 53226833603865152131992707)
              ·
                refine ⟨79840250405797728197989061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53226833603865152131992707 79840250405797728197989061)
                ·
                  refine ⟨14970046951087074037122949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79840250405797728197989061 14970046951087074037122949)
                  ·
                    refine ⟨2806883803328826381960553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14970046951087074037122949 2806883803328826381960553)
                    ·
                      refine ⟨2105162852496619786470415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2806883803328826381960553 2105162852496619786470415)
                      ·
                        rfl

theorem cell23_4099790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 4, 4, 2].length) (baseStart_4099790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4099790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4099790 prefixEnd_4099790 := by exact prefixLift 4099790
  have htrace : WordTrace (prefixWord ++ tailWord_4099790) baseStart_4099790 baseEnd_4099790 := by
    simpa [prefixWord, tailWord_4099790, baseEnd_4099790] using wordTrace_append hprefix tailTrace_4099790
  have hstable : (prefixWord ++ tailWord_4099790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099790).length < 2 ^ (prefixWord ++ tailWord_4099790).sum := by decide
  have hdescent : baseEnd_4099790 < baseStart_4099790 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099800 : List Nat := [2, 1, 2, 2, 3, 1, 4, 1, 3, 4]
def baseStart_4099800 : Nat := 118140960795 + 4099800 * 2 ^ 59
def prefixEnd_4099800 : Nat := 4983230072969 + 3 ^ 40 * 4099800 * 2
def baseEnd_4099800 : Nat := 701722662434388249115123

theorem tailTrace_4099800 : CollatzResearch.WordTrace tailWord_4099800 prefixEnd_4099800 701722662434388249115123 := by
  unfold tailWord_4099800
  simp only [CollatzResearch.WordTrace]
  refine ⟨74765995273566132470064427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99687993698088176626752569 74765995273566132470064427)
  ·
    refine ⟨112148992910349198705096641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74765995273566132470064427 112148992910349198705096641)
    ·
      refine ⟨84111744682761899028822481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112148992910349198705096641 84111744682761899028822481)
      ·
        refine ⟨63083808512071424271616861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84111744682761899028822481 63083808512071424271616861)
        ·
          refine ⟨23656428192026784101856323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63083808512071424271616861 23656428192026784101856323)
          ·
            refine ⟨35484642288040176152784485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23656428192026784101856323 35484642288040176152784485)
            ·
              refine ⟨6653370429007533028647091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35484642288040176152784485 6653370429007533028647091)
              ·
                refine ⟨9980055643511299542970637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6653370429007533028647091 9980055643511299542970637)
                ·
                  refine ⟨3742520866316737328613989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9980055643511299542970637 3742520866316737328613989)
                  ·
                    refine ⟨701722662434388249115123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3742520866316737328613989 701722662434388249115123)
                    ·
                      rfl

theorem cell23_4099800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 1, 3, 4].length) (baseStart_4099800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4099800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4099800 prefixEnd_4099800 := by exact prefixLift 4099800
  have htrace : WordTrace (prefixWord ++ tailWord_4099800) baseStart_4099800 baseEnd_4099800 := by
    simpa [prefixWord, tailWord_4099800, baseEnd_4099800] using wordTrace_append hprefix tailTrace_4099800
  have hstable : (prefixWord ++ tailWord_4099800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099800).length < 2 ^ (prefixWord ++ tailWord_4099800).sum := by decide
  have hdescent : baseEnd_4099800 < baseStart_4099800 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099823 : List Nat := [1, 1, 2, 1, 5, 1, 1, 1, 2, 5, 3]
def baseStart_4099823 : Nat := 118140960795 + 4099823 * 2 ^ 59
def prefixEnd_4099823 : Nat := 4983230072969 + 3 ^ 40 * 4099823 * 2
def baseEnd_4099823 : Nat := 2105179797358218157357763

theorem tailTrace_4099823 : CollatzResearch.WordTrace tailWord_4099823 prefixEnd_4099823 2105179797358218157357763 := by
  unfold tailWord_4099823
  simp only [CollatzResearch.WordTrace]
  refine ⟨149532829426048939868216123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99688552950699293245477415 149532829426048939868216123)
  ·
    refine ⟨224299244139073409802324185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149532829426048939868216123 224299244139073409802324185)
    ·
      refine ⟨168224433104305057351743139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224299244139073409802324185 168224433104305057351743139)
      ·
        refine ⟨252336649656457586027614709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168224433104305057351743139 252336649656457586027614709)
        ·
          refine ⟨23656560905292898690088879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 252336649656457586027614709 23656560905292898690088879)
          ·
            refine ⟨35484841357939348035133319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23656560905292898690088879 35484841357939348035133319)
            ·
              refine ⟨53227262036909022052699979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35484841357939348035133319 53227262036909022052699979)
              ·
                refine ⟨79840893055363533079049969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53227262036909022052699979 79840893055363533079049969)
                ·
                  refine ⟨59880669791522649809287477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79840893055363533079049969 59880669791522649809287477)
                  ·
                    refine ⟨5613812792955248419620701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59880669791522649809287477 5613812792955248419620701)
                    ·
                      refine ⟨2105179797358218157357763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5613812792955248419620701 2105179797358218157357763)
                      ·
                        rfl

theorem cell23_4099823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 5, 3].length) (baseStart_4099823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4099823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4099823 prefixEnd_4099823 := by exact prefixLift 4099823
  have htrace : WordTrace (prefixWord ++ tailWord_4099823) baseStart_4099823 baseEnd_4099823 := by
    simpa [prefixWord, tailWord_4099823, baseEnd_4099823] using wordTrace_append hprefix tailTrace_4099823
  have hstable : (prefixWord ++ tailWord_4099823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099823).length < 2 ^ (prefixWord ++ tailWord_4099823).sum := by decide
  have hdescent : baseEnd_4099823 < baseStart_4099823 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099877 : List Nat := [1, 3, 1, 2, 3, 4, 1, 2, 1, 5]
def baseStart_4099877 : Nat := 118140960795 + 4099877 * 2 ^ 59
def prefixEnd_4099877 : Nat := 4983230072969 + 3 ^ 40 * 4099877 * 2
def baseEnd_4099877 : Nat := 701735841771186982027505

theorem tailTrace_4099877 : CollatzResearch.WordTrace tailWord_4099877 prefixEnd_4099877 701735841771186982027505 := by
  unfold tailWord_4099877
  simp only [CollatzResearch.WordTrace]
  refine ⟨149534798967853307090681885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99689865978568871393787923 149534798967853307090681885)
  ·
    refine ⟨56075549612944990159005707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149534798967853307090681885 56075549612944990159005707)
    ·
      refine ⟨84113324419417485238508561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56075549612944990159005707 84113324419417485238508561)
      ·
        refine ⟨63084993314563113928881421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84113324419417485238508561 63084993314563113928881421)
        ·
          refine ⟨23656872492961167723330533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63084993314563113928881421 23656872492961167723330533)
          ·
            refine ⟨4435663592430218948124475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23656872492961167723330533 4435663592430218948124475)
            ·
              refine ⟨6653495388645328422186713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4435663592430218948124475 6653495388645328422186713)
              ·
                refine ⟨4990121541483996316640035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6653495388645328422186713 4990121541483996316640035)
                ·
                  refine ⟨7485182312225994474960053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4990121541483996316640035 7485182312225994474960053)
                  ·
                    refine ⟨701735841771186982027505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7485182312225994474960053 701735841771186982027505)
                    ·
                      rfl

theorem cell23_4099877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 2, 1, 5].length) (baseStart_4099877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4099877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4099877 prefixEnd_4099877 := by exact prefixLift 4099877
  have htrace : WordTrace (prefixWord ++ tailWord_4099877) baseStart_4099877 baseEnd_4099877 := by
    simpa [prefixWord, tailWord_4099877, baseEnd_4099877] using wordTrace_append hprefix tailTrace_4099877
  have hstable : (prefixWord ++ tailWord_4099877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099877).length < 2 ^ (prefixWord ++ tailWord_4099877).sum := by decide
  have hdescent : baseEnd_4099877 < baseStart_4099877 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099890 : List Nat := [3, 2, 1, 1, 3, 3, 1, 2, 1, 6]
def baseStart_4099890 : Nat := 118140960795 + 4099890 * 2 ^ 59
def prefixEnd_4099890 : Nat := 4983230072969 + 3 ^ 40 * 4099890 * 2
def baseEnd_4099890 : Nat := 701738066854023131739985

theorem tailTrace_4099890 : CollatzResearch.WordTrace tailWord_4099890 prefixEnd_4099890 701738066854023131739985 := by
  unfold tailWord_4099890
  simp only [CollatzResearch.WordTrace]
  refine ⟨37383818279201552577726281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99690182077870806873936749 37383818279201552577726281)
  ·
    refine ⟨28037863709401164433294711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37383818279201552577726281 28037863709401164433294711)
    ·
      refine ⟨42056795564101746649942067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28037863709401164433294711 42056795564101746649942067)
      ·
        refine ⟨63085193346152619974913101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42056795564101746649942067 63085193346152619974913101)
        ·
          refine ⟨23656947504807232490592413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63085193346152619974913101 23656947504807232490592413)
          ·
            refine ⟨8871355314302712183972155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23656947504807232490592413 8871355314302712183972155)
            ·
              refine ⟨13307032971454068275958233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8871355314302712183972155 13307032971454068275958233)
              ·
                refine ⟨9980274728590551206968675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13307032971454068275958233 9980274728590551206968675)
                ·
                  refine ⟨14970412092885826810453013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9980274728590551206968675 14970412092885826810453013)
                  ·
                    refine ⟨701738066854023131739985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14970412092885826810453013 701738066854023131739985)
                    ·
                      rfl

theorem cell23_4099890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 2, 1, 6].length) (baseStart_4099890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4099890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4099890 prefixEnd_4099890 := by exact prefixLift 4099890
  have htrace : WordTrace (prefixWord ++ tailWord_4099890) baseStart_4099890 baseEnd_4099890 := by
    simpa [prefixWord, tailWord_4099890, baseEnd_4099890] using wordTrace_append hprefix tailTrace_4099890
  have hstable : (prefixWord ++ tailWord_4099890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099890).length < 2 ^ (prefixWord ++ tailWord_4099890).sum := by decide
  have hdescent : baseEnd_4099890 < baseStart_4099890 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099900 : List Nat := [2, 2, 2, 2, 1, 1, 5, 1, 1, 1, 5]
def baseStart_4099900 : Nat := 118140960795 + 4099900 * 2 ^ 59
def prefixEnd_4099900 : Nat := 4983230072969 + 3 ^ 40 * 4099900 * 2
def baseEnd_4099900 : Nat := 2105219335368614356094909

theorem tailTrace_4099900 : CollatzResearch.WordTrace tailWord_4099900 prefixEnd_4099900 2105219335368614356094909 := by
  unfold tailWord_4099900
  simp only [CollatzResearch.WordTrace]
  refine ⟨74767818923384991009384577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99690425231179988012512769 74767818923384991009384577)
  ·
    refine ⟨56075864192538743257038433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74767818923384991009384577 56075864192538743257038433)
    ·
      refine ⟨42056898144404057442778825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56075864192538743257038433 42056898144404057442778825)
      ·
        refine ⟨31542673608303043082084119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42056898144404057442778825 31542673608303043082084119)
        ·
          refine ⟨47314010412454564623126179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31542673608303043082084119 47314010412454564623126179)
          ·
            refine ⟨70971015618681846934689269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47314010412454564623126179 70971015618681846934689269)
            ·
              refine ⟨6653532714251423150127119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70971015618681846934689269 6653532714251423150127119)
              ·
                refine ⟨9980299071377134725190679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6653532714251423150127119 9980299071377134725190679)
                ·
                  refine ⟨14970448607065702087786019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9980299071377134725190679 14970448607065702087786019)
                  ·
                    refine ⟨22455672910598553131679029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14970448607065702087786019 22455672910598553131679029)
                    ·
                      refine ⟨2105219335368614356094909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22455672910598553131679029 2105219335368614356094909)
                      ·
                        rfl

theorem cell23_4099900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 1, 1, 1, 5].length) (baseStart_4099900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4099900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4099900 prefixEnd_4099900 := by exact prefixLift 4099900
  have htrace : WordTrace (prefixWord ++ tailWord_4099900) baseStart_4099900 baseEnd_4099900 := by
    simpa [prefixWord, tailWord_4099900, baseEnd_4099900] using wordTrace_append hprefix tailTrace_4099900
  have hstable : (prefixWord ++ tailWord_4099900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099900).length < 2 ^ (prefixWord ++ tailWord_4099900).sum := by decide
  have hdescent : baseEnd_4099900 < baseStart_4099900 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099903 : List Nat := [1, 1, 2, 2, 6, 11]
def baseStart_4099903 : Nat := 118140960795 + 4099903 * 2 ^ 59
def prefixEnd_4099903 : Nat := 4983230072969 + 3 ^ 40 * 4099903 * 2
def baseEnd_4099903 : Nat := 8663460394282213351265

theorem tailTrace_4099903 : CollatzResearch.WordTrace tailWord_4099903 prefixEnd_4099903 8663460394282213351265 := by
  unfold tailWord_4099903
  simp only [CollatzResearch.WordTrace]
  refine ⟨149535747265759113531128363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99690498177172742354085575 149535747265759113531128363)
  ·
    refine ⟨224303620898638670296692545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149535747265759113531128363 224303620898638670296692545)
    ·
      refine ⟨168227715673979002722519409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224303620898638670296692545 168227715673979002722519409)
      ·
        refine ⟨126170786755484252041889557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168227715673979002722519409 126170786755484252041889557)
        ·
          refine ⟨5914255629163324314463573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 126170786755484252041889557 5914255629163324314463573)
          ·
            refine ⟨8663460394282213351265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 5914255629163324314463573 8663460394282213351265)
            ·
              rfl

theorem cell23_4099903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 11].length) (baseStart_4099903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4099903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4099903 prefixEnd_4099903 := by exact prefixLift 4099903
  have htrace : WordTrace (prefixWord ++ tailWord_4099903) baseStart_4099903 baseEnd_4099903 := by
    simpa [prefixWord, tailWord_4099903, baseEnd_4099903] using wordTrace_append hprefix tailTrace_4099903
  have hstable : (prefixWord ++ tailWord_4099903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099903).length < 2 ^ (prefixWord ++ tailWord_4099903).sum := by decide
  have hdescent : baseEnd_4099903 < baseStart_4099903 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099907 : List Nat := [1, 1, 1, 3, 1, 6, 2, 2, 2, 4]
def baseStart_4099907 : Nat := 118140960795 + 4099907 * 2 ^ 59
def prefixEnd_4099907 : Nat := 4983230072969 + 3 ^ 40 * 4099907 * 2
def baseEnd_4099907 : Nat := 701740976577731942902459

theorem tailTrace_4099907 : CollatzResearch.WordTrace tailWord_4099907 prefixEnd_4099907 701740976577731942902459 := by
  unfold tailWord_4099907
  simp only [CollatzResearch.WordTrace]
  refine ⟨149535893157744622214273975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99690595438496414809515983 149535893157744622214273975)
  ·
    refine ⟨224303839736616933321410963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149535893157744622214273975 224303839736616933321410963)
    ·
      refine ⟨336455759604925399982116445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224303839736616933321410963 336455759604925399982116445)
      ·
        refine ⟨126170909851847024993293667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 336455759604925399982116445 126170909851847024993293667)
        ·
          refine ⟨189256364777770537489940501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126170909851847024993293667 189256364777770537489940501)
          ·
            refine ⟨8871392098957993944840961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 189256364777770537489940501 8871392098957993944840961)
            ·
              refine ⟨6653544074218495458630721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8871392098957993944840961 6653544074218495458630721)
              ·
                refine ⟨4990158055663871593973041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6653544074218495458630721 4990158055663871593973041)
                ·
                  refine ⟨3742618541747903695479781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4990158055663871593973041 3742618541747903695479781)
                  ·
                    refine ⟨701740976577731942902459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3742618541747903695479781 701740976577731942902459)
                    ·
                      rfl

theorem cell23_4099907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 2, 2, 4].length) (baseStart_4099907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4099907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4099907 prefixEnd_4099907 := by exact prefixLift 4099907
  have htrace : WordTrace (prefixWord ++ tailWord_4099907) baseStart_4099907 baseEnd_4099907 := by
    simpa [prefixWord, tailWord_4099907, baseEnd_4099907] using wordTrace_append hprefix tailTrace_4099907
  have hstable : (prefixWord ++ tailWord_4099907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099907).length < 2 ^ (prefixWord ++ tailWord_4099907).sum := by decide
  have hdescent : baseEnd_4099907 < baseStart_4099907 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099927 : List Nat := [1, 1, 3, 2, 5, 1, 2, 1, 1, 2, 4]
def baseStart_4099927 : Nat := 118140960795 + 4099927 * 2 ^ 59
def prefixEnd_4099927 : Nat := 4983230072969 + 3 ^ 40 * 4099927 * 2
def baseEnd_4099927 : Nat := 2105233199346285750457285

theorem tailTrace_4099927 : CollatzResearch.WordTrace tailWord_4099927 prefixEnd_4099927 2105233199346285750457285 := by
  unfold tailWord_4099927
  simp only [CollatzResearch.WordTrace]
  refine ⟨149536622617672165630002035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99691081745114777086668023 149536622617672165630002035)
  ·
    refine ⟨224304933926508248445003053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149536622617672165630002035 224304933926508248445003053)
    ·
      refine ⟨84114350222440593166876145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224304933926508248445003053 84114350222440593166876145)
      ·
        refine ⟨63085762666830444875157109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84114350222440593166876145 63085762666830444875157109)
        ·
          refine ⟨5914290250015354207045979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63085762666830444875157109 5914290250015354207045979)
          ·
            refine ⟨8871435375023031310568969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5914290250015354207045979 8871435375023031310568969)
            ·
              refine ⟨6653576531267273482926727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8871435375023031310568969 6653576531267273482926727)
              ·
                refine ⟨9980364796900910224390091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6653576531267273482926727 9980364796900910224390091)
                ·
                  refine ⟨14970547195351365336585137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9980364796900910224390091 14970547195351365336585137)
                  ·
                    refine ⟨11227910396513524002438853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14970547195351365336585137 11227910396513524002438853)
                    ·
                      refine ⟨2105233199346285750457285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11227910396513524002438853 2105233199346285750457285)
                      ·
                        rfl

theorem cell23_4099927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 1, 1, 2, 4].length) (baseStart_4099927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4099927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4099927 prefixEnd_4099927 := by exact prefixLift 4099927
  have htrace : WordTrace (prefixWord ++ tailWord_4099927) baseStart_4099927 baseEnd_4099927 := by
    simpa [prefixWord, tailWord_4099927, baseEnd_4099927] using wordTrace_append hprefix tailTrace_4099927
  have hstable : (prefixWord ++ tailWord_4099927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099927).length < 2 ^ (prefixWord ++ tailWord_4099927).sum := by decide
  have hdescent : baseEnd_4099927 < baseStart_4099927 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099958 : List Nat := [5, 1, 1, 3, 3, 1, 1, 2, 2, 4]
def baseStart_4099958 : Nat := 118140960795 + 4099958 * 2 ^ 59
def prefixEnd_4099958 : Nat := 4983230072969 + 3 ^ 40 * 4099958 * 2
def baseEnd_4099958 : Nat := 701749705748858376389881

theorem tailTrace_4099958 : CollatzResearch.WordTrace tailWord_4099958 prefixEnd_4099958 701749705748858376389881 := by
  unfold tailWord_4099958
  simp only [CollatzResearch.WordTrace]
  refine ⟨9346109580034991120273783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99691835520373238616253685 9346109580034991120273783)
  ·
    refine ⟨14019164370052486680410675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9346109580034991120273783 14019164370052486680410675)
    ·
      refine ⟨21028746555078730020616013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14019164370052486680410675 21028746555078730020616013)
      ·
        refine ⟨7885779958154523757731005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21028746555078730020616013 7885779958154523757731005)
        ·
          refine ⟨2957167484307946409149127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7885779958154523757731005 2957167484307946409149127)
          ·
            refine ⟨4435751226461919613723691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2957167484307946409149127 4435751226461919613723691)
            ·
              refine ⟨6653626839692879420585537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4435751226461919613723691 6653626839692879420585537)
              ·
                refine ⟨4990220129769659565439153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6653626839692879420585537 4990220129769659565439153)
                ·
                  refine ⟨3742665097327244674079365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4990220129769659565439153 3742665097327244674079365)
                  ·
                    refine ⟨701749705748858376389881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3742665097327244674079365 701749705748858376389881)
                    ·
                      rfl

theorem cell23_4099958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 2, 2, 4].length) (baseStart_4099958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4099958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4099958 prefixEnd_4099958 := by exact prefixLift 4099958
  have htrace : WordTrace (prefixWord ++ tailWord_4099958) baseStart_4099958 baseEnd_4099958 := by
    simpa [prefixWord, tailWord_4099958, baseEnd_4099958] using wordTrace_append hprefix tailTrace_4099958
  have hstable : (prefixWord ++ tailWord_4099958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099958).length < 2 ^ (prefixWord ++ tailWord_4099958).sum := by decide
  have hdescent : baseEnd_4099958 < baseStart_4099958 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100004 : List Nat := [2, 3, 1, 2, 1, 3, 1, 2, 4, 2, 2]
def baseStart_4100004 : Nat := 118140960795 + 4100004 * 2 ^ 59
def prefixEnd_4100004 : Nat := 4983230072969 + 3 ^ 40 * 4100004 * 2
def baseEnd_4100004 : Nat := 2105272737356681949194431

theorem tailTrace_4100004 : CollatzResearch.WordTrace tailWord_4100004 prefixEnd_4100004 2105272737356681949194431 := by
  unfold tailWord_4100004
  simp only [CollatzResearch.WordTrace]
  refine ⟨74769715519196603890277533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99692954025595471853703377 74769715519196603890277533)
  ·
    refine ⟨28038643319698726458854075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74769715519196603890277533 28038643319698726458854075)
    ·
      refine ⟨42057964979548089688281113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28038643319698726458854075 42057964979548089688281113)
      ·
        refine ⟨31543473734661067266210835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42057964979548089688281113 31543473734661067266210835)
        ·
          refine ⟨47315210601991600899316253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31543473734661067266210835 47315210601991600899316253)
          ·
            refine ⟨17743203975746850337243595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47315210601991600899316253 17743203975746850337243595)
            ·
              refine ⟨26614805963620275505865393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17743203975746850337243595 26614805963620275505865393)
              ·
                refine ⟨19961104472715206629399045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26614805963620275505865393 19961104472715206629399045)
                ·
                  refine ⟨3742707088634101243012321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19961104472715206629399045 3742707088634101243012321)
                  ·
                    refine ⟨2807030316475575932259241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3742707088634101243012321 2807030316475575932259241)
                    ·
                      refine ⟨2105272737356681949194431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2807030316475575932259241 2105272737356681949194431)
                      ·
                        rfl

theorem cell23_4100004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 4, 2, 2].length) (baseStart_4100004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4100004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4100004 prefixEnd_4100004 := by exact prefixLift 4100004
  have htrace : WordTrace (prefixWord ++ tailWord_4100004) baseStart_4100004 baseEnd_4100004 := by
    simpa [prefixWord, tailWord_4100004, baseEnd_4100004] using wordTrace_append hprefix tailTrace_4100004
  have hstable : (prefixWord ++ tailWord_4100004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100004).length < 2 ^ (prefixWord ++ tailWord_4100004).sum := by decide
  have hdescent : baseEnd_4100004 < baseStart_4100004 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100007 : List Nat := [1, 1, 6, 1, 2, 2, 1, 1, 2, 1, 5]
def baseStart_4100007 : Nat := 118140960795 + 4100007 * 2 ^ 59
def prefixEnd_4100007 : Nat := 4983230072969 + 3 ^ 40 * 4100007 * 2
def baseEnd_4100007 : Nat := 2105274277798645437456917

theorem tailTrace_4100007 : CollatzResearch.WordTrace tailWord_4100007 prefixEnd_4100007 2105274277798645437456917 := by
  unfold tailWord_4100007
  simp only [CollatzResearch.WordTrace]
  refine ⟨149539540457382339292914275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99693026971588226195276183 149539540457382339292914275)
  ·
    refine ⟨224309310686073508939371413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149539540457382339292914275 224309310686073508939371413)
    ·
      refine ⟨10514498938409695731533035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 224309310686073508939371413 10514498938409695731533035)
      ·
        refine ⟨15771748407614543597299553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10514498938409695731533035 15771748407614543597299553)
        ·
          refine ⟨11828811305710907697974665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15771748407614543597299553 11828811305710907697974665)
          ·
            refine ⟨8871608479283180773480999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11828811305710907697974665 8871608479283180773480999)
            ·
              refine ⟨13307412718924771160221499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8871608479283180773480999 13307412718924771160221499)
              ·
                refine ⟨19961119078387156740332249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13307412718924771160221499 19961119078387156740332249)
                ·
                  refine ⟨14970839308790367555249187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19961119078387156740332249 14970839308790367555249187)
                  ·
                    refine ⟨22456258963185551332873781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14970839308790367555249187 22456258963185551332873781)
                    ·
                      refine ⟨2105274277798645437456917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22456258963185551332873781 2105274277798645437456917)
                      ·
                        rfl

theorem cell23_4100007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_4100007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4100007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4100007 prefixEnd_4100007 := by exact prefixLift 4100007
  have htrace : WordTrace (prefixWord ++ tailWord_4100007) baseStart_4100007 baseEnd_4100007 := by
    simpa [prefixWord, tailWord_4100007, baseEnd_4100007] using wordTrace_append hprefix tailTrace_4100007
  have hstable : (prefixWord ++ tailWord_4100007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100007).length < 2 ^ (prefixWord ++ tailWord_4100007).sum := by decide
  have hdescent : baseEnd_4100007 < baseStart_4100007 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100090 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 4, 4, 4]
def baseStart_4100090 : Nat := 118140960795 + 4100090 * 2 ^ 59
def prefixEnd_4100090 : Nat := 4983230072969 + 3 ^ 40 * 4100090 * 2
def baseEnd_4100090 : Nat := 2105316896692968612719035

theorem tailTrace_4100090 : CollatzResearch.WordTrace tailWord_4100090 prefixEnd_4100090 2105316896692968612719035 := by
  unfold tailWord_4100090
  simp only [CollatzResearch.WordTrace]
  refine ⟨37385641929020411117046431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99695045144054429645457149 37385641929020411117046431)
  ·
    refine ⟨56078462893530616675569647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37385641929020411117046431 56078462893530616675569647)
    ·
      refine ⟨84117694340295925013354471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56078462893530616675569647 84117694340295925013354471)
      ·
        refine ⟨126176541510443887520031707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84117694340295925013354471 126176541510443887520031707)
        ·
          refine ⟨189264812265665831280047561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126176541510443887520031707 189264812265665831280047561)
          ·
            refine ⟨141948609199249373460035671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189264812265665831280047561 141948609199249373460035671)
            ·
              refine ⟨212922913798874060190053507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141948609199249373460035671 212922913798874060190053507)
              ·
                refine ⟨319384370698311090285080261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212922913798874060190053507 319384370698311090285080261)
                ·
                  refine ⟨59884569505933329428452549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 319384370698311090285080261 59884569505933329428452549)
                  ·
                    refine ⟨11228356782362499267834853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59884569505933329428452549 11228356782362499267834853)
                    ·
                      refine ⟨2105316896692968612719035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11228356782362499267834853 2105316896692968612719035)
                      ·
                        rfl

theorem cell23_4100090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 4, 4, 4].length) (baseStart_4100090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4100090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4100090 prefixEnd_4100090 := by exact prefixLift 4100090
  have htrace : WordTrace (prefixWord ++ tailWord_4100090) baseStart_4100090 baseEnd_4100090 := by
    simpa [prefixWord, tailWord_4100090, baseEnd_4100090] using wordTrace_append hprefix tailTrace_4100090
  have hstable : (prefixWord ++ tailWord_4100090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100090).length < 2 ^ (prefixWord ++ tailWord_4100090).sum := by decide
  have hdescent : baseEnd_4100090 < baseStart_4100090 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100097 : List Nat := [1, 2, 4, 1, 2, 1, 2, 2, 1, 4, 3]
def baseStart_4100097 : Nat := 118140960795 + 4100097 * 2 ^ 59
def prefixEnd_4100097 : Nat := 4983230072969 + 3 ^ 40 * 4100097 * 2
def baseEnd_4100097 : Nat := 2105320491057550085331503

theorem tailTrace_4100097 : CollatzResearch.WordTrace tailWord_4100097 prefixEnd_4100097 2105320491057550085331503 := by
  unfold tailWord_4100097
  simp only [CollatzResearch.WordTrace]
  refine ⟨149542823027056284663690545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99695215351370856442460363 149542823027056284663690545)
  ·
    refine ⟨112157117270292213497767909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149542823027056284663690545 112157117270292213497767909)
    ·
      refine ⟨21029459488179790030831483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112157117270292213497767909 21029459488179790030831483)
      ·
        refine ⟨31544189232269685046247225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21029459488179790030831483 31544189232269685046247225)
        ·
          refine ⟨23658141924202263784685419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31544189232269685046247225 23658141924202263784685419)
          ·
            refine ⟨35487212886303395677028129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23658141924202263784685419 35487212886303395677028129)
            ·
              refine ⟨26615409664727546757771097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35487212886303395677028129 26615409664727546757771097)
              ·
                refine ⟨19961557248545660068328323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26615409664727546757771097 19961557248545660068328323)
                ·
                  refine ⟨29942335872818490102492485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19961557248545660068328323 29942335872818490102492485)
                  ·
                    refine ⟨5614187976153466894217341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29942335872818490102492485 5614187976153466894217341)
                    ·
                      refine ⟨2105320491057550085331503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5614187976153466894217341 2105320491057550085331503)
                      ·
                        rfl

theorem cell23_4100097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 4, 3].length) (baseStart_4100097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4100097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4100097 prefixEnd_4100097 := by exact prefixLift 4100097
  have htrace : WordTrace (prefixWord ++ tailWord_4100097) baseStart_4100097 baseEnd_4100097 := by
    simpa [prefixWord, tailWord_4100097, baseEnd_4100097] using wordTrace_append hprefix tailTrace_4100097
  have hstable : (prefixWord ++ tailWord_4100097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100097).length < 2 ^ (prefixWord ++ tailWord_4100097).sum := by decide
  have hdescent : baseEnd_4100097 < baseStart_4100097 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100140 : List Nat := [2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 7]
def baseStart_4100140 : Nat := 118140960795 + 4100140 * 2 ^ 59
def prefixEnd_4100140 : Nat := 4983230072969 + 3 ^ 40 * 4100140 * 2
def baseEnd_4100140 : Nat := 2105342570725693417093805

theorem tailTrace_4100140 : CollatzResearch.WordTrace tailWord_4100140 prefixEnd_4100140 2105342570725693417093805 := by
  unfold tailWord_4100140
  simp only [CollatzResearch.WordTrace]
  refine ⟨74772195682950251503752937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99696260910600335338337249 74772195682950251503752937)
  ·
    refine ⟨56079146762212688627814703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74772195682950251503752937 56079146762212688627814703)
    ·
      refine ⟨84118720143319032941722055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56079146762212688627814703 84118720143319032941722055)
      ·
        refine ⟨126178080214978549412583083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84118720143319032941722055 126178080214978549412583083)
        ·
          refine ⟨189267120322467824118874625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126178080214978549412583083 189267120322467824118874625)
          ·
            refine ⟨141950340241850868089155969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189267120322467824118874625 141950340241850868089155969)
            ·
              refine ⟨106462755181388151066866977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141950340241850868089155969 106462755181388151066866977)
              ·
                refine ⟨79847066386041113300150233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106462755181388151066866977 79847066386041113300150233)
                ·
                  refine ⟨59885299789530834975112675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79847066386041113300150233 59885299789530834975112675)
                  ·
                    refine ⟨89827949684296252462669013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59885299789530834975112675 89827949684296252462669013)
                    ·
                      refine ⟨2105342570725693417093805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 89827949684296252462669013 2105342570725693417093805)
                      ·
                        rfl

theorem cell23_4100140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 7].length) (baseStart_4100140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4100140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4100140 prefixEnd_4100140 := by exact prefixLift 4100140
  have htrace : WordTrace (prefixWord ++ tailWord_4100140) baseStart_4100140 baseEnd_4100140 := by
    simpa [prefixWord, tailWord_4100140, baseEnd_4100140] using wordTrace_append hprefix tailTrace_4100140
  have hstable : (prefixWord ++ tailWord_4100140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100140).length < 2 ^ (prefixWord ++ tailWord_4100140).sum := by decide
  have hdescent : baseEnd_4100140 < baseStart_4100140 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100144 : List Nat := [2, 1, 1, 1, 2, 5, 1, 3, 3, 1, 3]
def baseStart_4100144 : Nat := 118140960795 + 4100144 * 2 ^ 59
def prefixEnd_4100144 : Nat := 4983230072969 + 3 ^ 40 * 4100144 * 2
def baseEnd_4100144 : Nat := 2105344624648311401443787

theorem tailTrace_4100144 : CollatzResearch.WordTrace tailWord_4100144 prefixEnd_4100144 2105344624648311401443787 := by
  unfold tailWord_4100144
  simp only [CollatzResearch.WordTrace]
  refine ⟨74772268628943005845325743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99696358171924007793767657 74772268628943005845325743)
  ·
    refine ⟨112158402943414508767988615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74772268628943005845325743 112158402943414508767988615)
    ·
      refine ⟨168237604415121763151982923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112158402943414508767988615 168237604415121763151982923)
      ·
        refine ⟨252356406622682644727974385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168237604415121763151982923 252356406622682644727974385)
        ·
          refine ⟨189267304967011983545980789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252356406622682644727974385 189267304967011983545980789)
          ·
            refine ⟨17743809840657373457435699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 189267304967011983545980789 17743809840657373457435699)
            ·
              refine ⟨26615714760986060186153549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17743809840657373457435699 26615714760986060186153549)
              ·
                refine ⟨9980893035369772569807581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26615714760986060186153549 9980893035369772569807581)
                ·
                  refine ⟨3742834888263664713677843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9980893035369772569807581 3742834888263664713677843)
                  ·
                    refine ⟨5614252332395497070516765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3742834888263664713677843 5614252332395497070516765)
                    ·
                      refine ⟨2105344624648311401443787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5614252332395497070516765 2105344624648311401443787)
                      ·
                        rfl

theorem cell23_4100144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 3, 3, 1, 3].length) (baseStart_4100144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4100144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4100144 prefixEnd_4100144 := by exact prefixLift 4100144
  have htrace : WordTrace (prefixWord ++ tailWord_4100144) baseStart_4100144 baseEnd_4100144 := by
    simpa [prefixWord, tailWord_4100144, baseEnd_4100144] using wordTrace_append hprefix tailTrace_4100144
  have hstable : (prefixWord ++ tailWord_4100144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100144).length < 2 ^ (prefixWord ++ tailWord_4100144).sum := by decide
  have hdescent : baseEnd_4100144 < baseStart_4100144 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100161 : List Nat := [1, 2, 5, 1, 2, 1, 2, 2, 3, 1, 3]
def baseStart_4100161 : Nat := 118140960795 + 4100161 * 2 ^ 59
def prefixEnd_4100161 : Nat := 4983230072969 + 3 ^ 40 * 4100161 * 2
def baseEnd_4100161 : Nat := 2105353353819437834931209

theorem tailTrace_4100161 : CollatzResearch.WordTrace tailWord_4100161 prefixEnd_4100161 2105353353819437834931209 := by
  unfold tailWord_4100161
  simp only [CollatzResearch.WordTrace]
  refine ⟨149545157298824423594020337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99696771532549615729346891 149545157298824423594020337)
  ·
    refine ⟨112158867974118317695515253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149545157298824423594020337 112158867974118317695515253)
    ·
      refine ⟨10514893872573592283954555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 112158867974118317695515253 10514893872573592283954555)
      ·
        refine ⟨15772340808860388425931833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10514893872573592283954555 15772340808860388425931833)
        ·
          refine ⟨11829255606645291319448875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15772340808860388425931833 11829255606645291319448875)
          ·
            refine ⟨17743883409967936979173313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11829255606645291319448875 17743883409967936979173313)
            ·
              refine ⟨13307912557475952734379985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17743883409967936979173313 13307912557475952734379985)
              ·
                refine ⟨9980934418106964550784989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13307912557475952734379985 9980934418106964550784989)
                ·
                  refine ⟨3742850406790111706544371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9980934418106964550784989 3742850406790111706544371)
                  ·
                    refine ⟨5614275610185167559816557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3742850406790111706544371 5614275610185167559816557)
                    ·
                      refine ⟨2105353353819437834931209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5614275610185167559816557 2105353353819437834931209)
                      ·
                        rfl

theorem cell23_4100161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_4100161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4100161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4100161 prefixEnd_4100161 := by exact prefixLift 4100161
  have htrace : WordTrace (prefixWord ++ tailWord_4100161) baseStart_4100161 baseEnd_4100161 := by
    simpa [prefixWord, tailWord_4100161, baseEnd_4100161] using wordTrace_append hprefix tailTrace_4100161
  have hstable : (prefixWord ++ tailWord_4100161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100161).length < 2 ^ (prefixWord ++ tailWord_4100161).sum := by decide
  have hdescent : baseEnd_4100161 < baseStart_4100161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100184 : List Nat := [2, 1, 2, 2, 1, 4, 2, 3, 1, 1, 4]
def baseStart_4100184 : Nat := 118140960795 + 4100184 * 2 ^ 59
def prefixEnd_4100184 : Nat := 4983230072969 + 3 ^ 40 * 4100184 * 2
def baseEnd_4100184 : Nat := 2105365163874491244943603

theorem tailTrace_4100184 : CollatzResearch.WordTrace tailWord_4100184 prefixEnd_4100184 2105365163874491244943603 := by
  unfold tailWord_4100184
  simp only [CollatzResearch.WordTrace]
  refine ⟨74772998088870549261053803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99697330785160732348071737 74772998088870549261053803)
  ·
    refine ⟨112159497133305823891580705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74772998088870549261053803 112159497133305823891580705)
    ·
      refine ⟨84119622849979367918685529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112159497133305823891580705 84119622849979367918685529)
      ·
        refine ⟨63089717137484525939014147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84119622849979367918685529 63089717137484525939014147)
        ·
          refine ⟨94634575706226788908521221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63089717137484525939014147 94634575706226788908521221)
          ·
            refine ⟨17743982944917522920347729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94634575706226788908521221 17743982944917522920347729)
            ·
              refine ⟨13307987208688142190260797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17743982944917522920347729 13307987208688142190260797)
              ·
                refine ⟨4990495203258053321347799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13307987208688142190260797 4990495203258053321347799)
                ·
                  refine ⟨7485742804887079982021699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4990495203258053321347799 7485742804887079982021699)
                  ·
                    refine ⟨11228614207330619973032549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7485742804887079982021699 11228614207330619973032549)
                    ·
                      refine ⟨2105365163874491244943603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11228614207330619973032549 2105365163874491244943603)
                      ·
                        rfl

theorem cell23_4100184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 3, 1, 1, 4].length) (baseStart_4100184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4100184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4100184 prefixEnd_4100184 := by exact prefixLift 4100184
  have htrace : WordTrace (prefixWord ++ tailWord_4100184) baseStart_4100184 baseEnd_4100184 := by
    simpa [prefixWord, tailWord_4100184, baseEnd_4100184] using wordTrace_append hprefix tailTrace_4100184
  have hstable : (prefixWord ++ tailWord_4100184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100184).length < 2 ^ (prefixWord ++ tailWord_4100184).sum := by decide
  have hdescent : baseEnd_4100184 < baseStart_4100184 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100197 : List Nat := [1, 3, 1, 3, 2, 2, 1, 2, 1, 1, 6]
def baseStart_4100197 : Nat := 118140960795 + 4100197 * 2 ^ 59
def prefixEnd_4100197 : Nat := 4983230072969 + 3 ^ 40 * 4100197 * 2
def baseEnd_4100197 : Nat := 2105371839122999694081043

theorem tailTrace_4100197 : CollatzResearch.WordTrace tailWord_4100197 prefixEnd_4100197 2105371839122999694081043 := by
  unfold tailWord_4100197
  simp only [CollatzResearch.WordTrace]
  refine ⟨149546470326694001742330845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99697646884462667828220563 149546470326694001742330845)
  ·
    refine ⟨56079926372510250653374067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149546470326694001742330845 56079926372510250653374067)
    ·
      refine ⟨84119889558765375980061101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56079926372510250653374067 84119889558765375980061101)
      ·
        refine ⟨31544958584537015992522913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84119889558765375980061101 31544958584537015992522913)
        ·
          refine ⟨23658718938402761994392185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31544958584537015992522913 23658718938402761994392185)
          ·
            refine ⟨17744039203802071495794139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23658718938402761994392185 17744039203802071495794139)
            ·
              refine ⟨26616058805703107243691209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17744039203802071495794139 26616058805703107243691209)
              ·
                refine ⟨19962044104277330432768407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26616058805703107243691209 19962044104277330432768407)
                ·
                  refine ⟨29943066156415995649152611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19962044104277330432768407 29943066156415995649152611)
                  ·
                    refine ⟨44914599234623993473728917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29943066156415995649152611 44914599234623993473728917)
                    ·
                      refine ⟨2105371839122999694081043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44914599234623993473728917 2105371839122999694081043)
                      ·
                        rfl

theorem cell23_4100197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_4100197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4100197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4100197 prefixEnd_4100197 := by exact prefixLift 4100197
  have htrace : WordTrace (prefixWord ++ tailWord_4100197) baseStart_4100197 baseEnd_4100197 := by
    simpa [prefixWord, tailWord_4100197, baseEnd_4100197] using wordTrace_append hprefix tailTrace_4100197
  have hstable : (prefixWord ++ tailWord_4100197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100197).length < 2 ^ (prefixWord ++ tailWord_4100197).sum := by decide
  have hdescent : baseEnd_4100197 < baseStart_4100197 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100207 : List Nat := [1, 1, 2, 1, 3, 5, 2, 8]
def baseStart_4100207 : Nat := 118140960795 + 4100207 * 2 ^ 59
def prefixEnd_4100207 : Nat := 4983230072969 + 3 ^ 40 * 4100207 * 2
def baseEnd_4100207 : Nat := 77976924960353505739111

theorem tailTrace_4100207 : CollatzResearch.WordTrace tailWord_4100207 prefixEnd_4100207 77976924960353505739111 := by
  unfold tailWord_4100207
  simp only [CollatzResearch.WordTrace]
  refine ⟨149546835056657773450194875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99697890037771848966796583 149546835056657773450194875)
  ·
    refine ⟨224320252584986660175292313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149546835056657773450194875 224320252584986660175292313)
    ·
      refine ⟨168240189438739995131469235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224320252584986660175292313 168240189438739995131469235)
      ·
        refine ⟨252360284158109992697203853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168240189438739995131469235 252360284158109992697203853)
        ·
          refine ⟨94635106559291247261451445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252360284158109992697203853 94635106559291247261451445)
          ·
            refine ⟨8872041239933554430761073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94635106559291247261451445 8872041239933554430761073)
            ·
              refine ⟨6654030929950165823070805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8872041239933554430761073 6654030929950165823070805)
              ·
                refine ⟨77976924960353505739111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6654030929950165823070805 77976924960353505739111)
                ·
                  rfl

theorem cell23_4100207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 8].length) (baseStart_4100207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4100207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4100207 prefixEnd_4100207 := by exact prefixLift 4100207
  have htrace : WordTrace (prefixWord ++ tailWord_4100207) baseStart_4100207 baseEnd_4100207 := by
    simpa [prefixWord, tailWord_4100207, baseEnd_4100207] using wordTrace_append hprefix tailTrace_4100207
  have hstable : (prefixWord ++ tailWord_4100207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100207).length < 2 ^ (prefixWord ++ tailWord_4100207).sum := by decide
  have hdescent : baseEnd_4100207 < baseStart_4100207 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100214 : List Nat := [5, 1, 1, 2, 1, 2, 2, 1, 1, 1, 6]
def baseStart_4100214 : Nat := 118140960795 + 4100214 * 2 ^ 59
def prefixEnd_4100214 : Nat := 4983230072969 + 3 ^ 40 * 4100214 * 2
def baseEnd_4100214 : Nat := 2105380568294126127568465

theorem tailTrace_4100214 : CollatzResearch.WordTrace tailWord_4100214 prefixEnd_4100214 2105380568294126127568465 := by
  unfold tailWord_4100214
  simp only [CollatzResearch.WordTrace]
  refine ⟨9346693147977025852856231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99698060245088275763799797 9346693147977025852856231)
  ·
    refine ⟨14020039721965538779284347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9346693147977025852856231 14020039721965538779284347)
    ·
      refine ⟨21030059582948308168926521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14020039721965538779284347 21030059582948308168926521)
      ·
        refine ⟨15772544687211231126694891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21030059582948308168926521 15772544687211231126694891)
        ·
          refine ⟨23658817030816846690042337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15772544687211231126694891 23658817030816846690042337)
          ·
            refine ⟨17744112773112635017531753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23658817030816846690042337 17744112773112635017531753)
            ·
              refine ⟨13308084579834476263148815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17744112773112635017531753 13308084579834476263148815)
              ·
                refine ⟨19962126869751714394723223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13308084579834476263148815 19962126869751714394723223)
                ·
                  refine ⟨29943190304627571592084835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19962126869751714394723223 29943190304627571592084835)
                  ·
                    refine ⟨44914785456941357388127253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29943190304627571592084835 44914785456941357388127253)
                    ·
                      refine ⟨2105380568294126127568465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44914785456941357388127253 2105380568294126127568465)
                      ·
                        rfl

theorem cell23_4100214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_4100214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4100214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4100214 prefixEnd_4100214 := by exact prefixLift 4100214
  have htrace : WordTrace (prefixWord ++ tailWord_4100214) baseStart_4100214 baseEnd_4100214 := by
    simpa [prefixWord, tailWord_4100214, baseEnd_4100214] using wordTrace_append hprefix tailTrace_4100214
  have hstable : (prefixWord ++ tailWord_4100214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100214).length < 2 ^ (prefixWord ++ tailWord_4100214).sum := by decide
  have hdescent : baseEnd_4100214 < baseStart_4100214 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100221 : List Nat := [1, 4, 1, 1, 3, 2, 3, 2, 1, 2, 3]
def baseStart_4100221 : Nat := 118140960795 + 4100221 * 2 ^ 59
def prefixEnd_4100221 : Nat := 4983230072969 + 3 ^ 40 * 4100221 * 2
def baseEnd_4100221 : Nat := 2105384162658707600180933

theorem tailTrace_4100221 : CollatzResearch.WordTrace tailWord_4100221 prefixEnd_4100221 2105384162658707600180933 := by
  unfold tailWord_4100221
  simp only [CollatzResearch.WordTrace]
  refine ⟨149547345678607053841204517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99698230452404702560803011 149547345678607053841204517)
  ·
    refine ⟨28040127314738822595225847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149547345678607053841204517 28040127314738822595225847)
    ·
      refine ⟨42060190972108233892838771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28040127314738822595225847 42060190972108233892838771)
      ·
        refine ⟨63090286458162350839258157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42060190972108233892838771 63090286458162350839258157)
        ·
          refine ⟨23658857421810881564721809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63090286458162350839258157 23658857421810881564721809)
          ·
            refine ⟨17744143066358161173541357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23658857421810881564721809 17744143066358161173541357)
            ·
              refine ⟨6654053649884310440078009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17744143066358161173541357 6654053649884310440078009)
              ·
                refine ⟨4990540237413232830058507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6654053649884310440078009 4990540237413232830058507)
                ·
                  refine ⟨7485810356119849245087761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4990540237413232830058507 7485810356119849245087761)
                  ·
                    refine ⟨5614357767089886933815821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7485810356119849245087761 5614357767089886933815821)
                    ·
                      refine ⟨2105384162658707600180933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5614357767089886933815821 2105384162658707600180933)
                      ·
                        rfl

theorem cell23_4100221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 2, 1, 2, 3].length) (baseStart_4100221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4100221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4100221 prefixEnd_4100221 := by exact prefixLift 4100221
  have htrace : WordTrace (prefixWord ++ tailWord_4100221) baseStart_4100221 baseEnd_4100221 := by
    simpa [prefixWord, tailWord_4100221, baseEnd_4100221] using wordTrace_append hprefix tailTrace_4100221
  have hstable : (prefixWord ++ tailWord_4100221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100221).length < 2 ^ (prefixWord ++ tailWord_4100221).sum := by decide
  have hdescent : baseEnd_4100221 < baseStart_4100221 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100234 : List Nat := [3, 1, 2, 3, 1, 2, 1, 1, 3, 3, 3]
def baseStart_4100234 : Nat := 118140960795 + 4100234 * 2 ^ 59
def prefixEnd_4100234 : Nat := 4983230072969 + 3 ^ 40 * 4100234 * 2
def baseEnd_4100234 : Nat := 2105390837907216049318373

theorem tailTrace_4100234 : CollatzResearch.WordTrace tailWord_4100234 prefixEnd_4100234 2105390837907216049318373 := by
  unfold tailWord_4100234
  simp only [CollatzResearch.WordTrace]
  refine ⟨37386954956889989265356939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99698546551706638040951837 37386954956889989265356939)
  ·
    refine ⟨56080432435334983898035409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37386954956889989265356939 56080432435334983898035409)
    ·
      refine ⟨42060324326501237923526557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56080432435334983898035409 42060324326501237923526557)
      ·
        refine ⟨15772621622437964221322459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42060324326501237923526557 15772621622437964221322459)
        ·
          refine ⟨23658932433656946331983689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15772621622437964221322459 23658932433656946331983689)
          ·
            refine ⟨17744199325242709748987767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23658932433656946331983689 17744199325242709748987767)
            ·
              refine ⟨26616298987864064623481651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17744199325242709748987767 26616298987864064623481651)
              ·
                refine ⟨39924448481796096935222477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26616298987864064623481651 39924448481796096935222477)
                ·
                  refine ⟨14971668180673536350708429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39924448481796096935222477 14971668180673536350708429)
                  ·
                    refine ⟨5614375567752576131515661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14971668180673536350708429 5614375567752576131515661)
                    ·
                      refine ⟨2105390837907216049318373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5614375567752576131515661 2105390837907216049318373)
                      ·
                        rfl

theorem cell23_4100234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_4100234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4100234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4100234 prefixEnd_4100234 := by exact prefixLift 4100234
  have htrace : WordTrace (prefixWord ++ tailWord_4100234) baseStart_4100234 baseEnd_4100234 := by
    simpa [prefixWord, tailWord_4100234, baseEnd_4100234] using wordTrace_append hprefix tailTrace_4100234
  have hstable : (prefixWord ++ tailWord_4100234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100234).length < 2 ^ (prefixWord ++ tailWord_4100234).sum := by decide
  have hdescent : baseEnd_4100234 < baseStart_4100234 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100238 : List Nat := [4, 1, 1, 3, 4, 1, 1, 1, 1, 1, 5]
def baseStart_4100238 : Nat := 118140960795 + 4100238 * 2 ^ 59
def prefixEnd_4100238 : Nat := 4983230072969 + 3 ^ 40 * 4100238 * 2
def baseEnd_4100238 : Nat := 2105392891829834033668355

theorem tailTrace_4100238 : CollatzResearch.WordTrace tailWord_4100238 prefixEnd_4100238 2105392891829834033668355 := by
  unfold tailWord_4100238
  simp only [CollatzResearch.WordTrace]
  refine ⟨18693495714943183218071671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99698643813030310496382245 18693495714943183218071671)
  ·
    refine ⟨28040243572414774827107507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18693495714943183218071671 28040243572414774827107507)
    ·
      refine ⟨42060365358622162240661261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28040243572414774827107507 42060365358622162240661261)
      ·
        refine ⟨15772637009483310840247973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42060365358622162240661261 15772637009483310840247973)
        ·
          refine ⟨2957369439278120782546495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15772637009483310840247973 2957369439278120782546495)
          ·
            refine ⟨4436054158917181173819743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2957369439278120782546495 4436054158917181173819743)
            ·
              refine ⟨6654081238375771760729615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4436054158917181173819743 6654081238375771760729615)
              ·
                refine ⟨9981121857563657641094423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6654081238375771760729615 9981121857563657641094423)
                ·
                  refine ⟨14971682786345486461641635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9981121857563657641094423 14971682786345486461641635)
                  ·
                    refine ⟨22457524179518229692462453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14971682786345486461641635 22457524179518229692462453)
                    ·
                      refine ⟨2105392891829834033668355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22457524179518229692462453 2105392891829834033668355)
                      ·
                        rfl

theorem cell23_4100238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 1, 1, 1, 5].length) (baseStart_4100238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4100238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4100238 prefixEnd_4100238 := by exact prefixLift 4100238
  have htrace : WordTrace (prefixWord ++ tailWord_4100238) baseStart_4100238 baseEnd_4100238 := by
    simpa [prefixWord, tailWord_4100238, baseEnd_4100238] using wordTrace_append hprefix tailTrace_4100238
  have hstable : (prefixWord ++ tailWord_4100238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100238).length < 2 ^ (prefixWord ++ tailWord_4100238).sum := by decide
  have hdescent : baseEnd_4100238 < baseStart_4100238 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100246 : List Nat := [5, 3, 2, 1, 1, 1, 1, 4, 1, 1, 3]
def baseStart_4100246 : Nat := 118140960795 + 4100246 * 2 ^ 59
def prefixEnd_4100246 : Nat := 4983230072969 + 3 ^ 40 * 4100246 * 2
def baseEnd_4100246 : Nat := 2105396999675070002368319

theorem tailTrace_4100246 : CollatzResearch.WordTrace tailWord_4100246 prefixEnd_4100246 2105396999675070002368319 := by
  unfold tailWord_4100246
  simp only [CollatzResearch.WordTrace]
  refine ⟨9346766093969780194429037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99698838335677655407243061 9346766093969780194429037)
  ·
    refine ⟨3505037285238667572910889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9346766093969780194429037 3505037285238667572910889)
    ·
      refine ⟨2628777963929000679683167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3505037285238667572910889 2628777963929000679683167)
      ·
        refine ⟨3943166945893501019524751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2628777963929000679683167 3943166945893501019524751)
        ·
          refine ⟨5914750418840251529287127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3943166945893501019524751 5914750418840251529287127)
          ·
            refine ⟨8872125628260377293930691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5914750418840251529287127 8872125628260377293930691)
            ·
              refine ⟨13308188442390565940896037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8872125628260377293930691 13308188442390565940896037)
              ·
                refine ⟨2495285332948231113918007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13308188442390565940896037 2495285332948231113918007)
                ·
                  refine ⟨3742927999422346670877011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2495285332948231113918007 3742927999422346670877011)
                  ·
                    refine ⟨5614391999133520006315517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3742927999422346670877011 5614391999133520006315517)
                    ·
                      refine ⟨2105396999675070002368319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5614391999133520006315517 2105396999675070002368319)
                      ·
                        rfl

theorem cell23_4100246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_4100246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4100246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4100246 prefixEnd_4100246 := by exact prefixLift 4100246
  have htrace : WordTrace (prefixWord ++ tailWord_4100246) baseStart_4100246 baseEnd_4100246 := by
    simpa [prefixWord, tailWord_4100246, baseEnd_4100246] using wordTrace_append hprefix tailTrace_4100246
  have hstable : (prefixWord ++ tailWord_4100246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100246).length < 2 ^ (prefixWord ++ tailWord_4100246).sum := by decide
  have hdescent : baseEnd_4100246 < baseStart_4100246 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100287 : List Nat := [1, 1, 2, 2, 2, 2, 1, 1, 3, 4, 4]
def baseStart_4100287 : Nat := 118140960795 + 4100287 * 2 ^ 59
def prefixEnd_4100287 : Nat := 4983230072969 + 3 ^ 40 * 4100287 * 2
def baseEnd_4100287 : Nat := 2105418052381904341955629

theorem tailTrace_4100287 : CollatzResearch.WordTrace tailWord_4100287 prefixEnd_4100287 2105418052381904341955629 := by
  unfold tailWord_4100287
  simp only [CollatzResearch.WordTrace]
  refine ⟨149549752896367947113107115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99699835264245298075404743 149549752896367947113107115)
  ·
    refine ⟨224324629344551920669660673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149549752896367947113107115 224324629344551920669660673)
    ·
      refine ⟨168243472008413940502245505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224324629344551920669660673 168243472008413940502245505)
      ·
        refine ⟨126182604006310455376684129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168243472008413940502245505 126182604006310455376684129)
        ·
          refine ⟨94636953004732841532513097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126182604006310455376684129 94636953004732841532513097)
          ·
            refine ⟨70977714753549631149384823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94636953004732841532513097 70977714753549631149384823)
            ·
              refine ⟨106466572130324446724077235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70977714753549631149384823 106466572130324446724077235)
              ·
                refine ⟨159699858195486670086115853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106466572130324446724077235 159699858195486670086115853)
                ·
                  refine ⟨59887446823307501282293445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 159699858195486670086115853 59887446823307501282293445)
                  ·
                    refine ⟨11228896279370156490430021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59887446823307501282293445 11228896279370156490430021)
                    ·
                      refine ⟨2105418052381904341955629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11228896279370156490430021 2105418052381904341955629)
                      ·
                        rfl

theorem cell23_4100287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 4, 4].length) (baseStart_4100287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4100287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4100287 prefixEnd_4100287 := by exact prefixLift 4100287
  have htrace : WordTrace (prefixWord ++ tailWord_4100287) baseStart_4100287 baseEnd_4100287 := by
    simpa [prefixWord, tailWord_4100287, baseEnd_4100287] using wordTrace_append hprefix tailTrace_4100287
  have hstable : (prefixWord ++ tailWord_4100287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100287).length < 2 ^ (prefixWord ++ tailWord_4100287).sum := by decide
  have hdescent : baseEnd_4100287 < baseStart_4100287 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100348 : List Nat := [2, 2, 2, 1, 4, 3, 1, 3, 5]
def baseStart_4100348 : Nat := 118140960795 + 4100348 * 2 ^ 59
def prefixEnd_4100348 : Nat := 4983230072969 + 3 ^ 40 * 4100348 * 2
def baseEnd_4100348 : Nat := 233938819411314289254761

theorem tailTrace_4100348 : CollatzResearch.WordTrace tailWord_4100348 prefixEnd_4100348 233938819411314289254761 := by
  unfold tailWord_4100348
  simp only [CollatzResearch.WordTrace]
  refine ⟨74775988874573477265538849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99701318499431303020718465 74775988874573477265538849)
  ·
    refine ⟨56081991655930107949154137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74775988874573477265538849 56081991655930107949154137)
    ·
      refine ⟨42061493741947580961865603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56081991655930107949154137 42061493741947580961865603)
      ·
        refine ⟨63092240612921371442798405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42061493741947580961865603 63092240612921371442798405)
        ·
          refine ⟨11829795114922757145524701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63092240612921371442798405 11829795114922757145524701)
          ·
            refine ⟨4436173168096033929571763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11829795114922757145524701 4436173168096033929571763)
            ·
              refine ⟨6654259752144050894357645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4436173168096033929571763 6654259752144050894357645)
              ·
                refine ⟨2495347407054019085384117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6654259752144050894357645 2495347407054019085384117)
                ·
                  refine ⟨233938819411314289254761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2495347407054019085384117 233938819411314289254761)
                  ·
                    rfl

theorem cell23_4100348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 3, 5].length) (baseStart_4100348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4100348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4100348 prefixEnd_4100348 := by exact prefixLift 4100348
  have htrace : WordTrace (prefixWord ++ tailWord_4100348) baseStart_4100348 baseEnd_4100348 := by
    simpa [prefixWord, tailWord_4100348, baseEnd_4100348] using wordTrace_append hprefix tailTrace_4100348
  have hstable : (prefixWord ++ tailWord_4100348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100348).length < 2 ^ (prefixWord ++ tailWord_4100348).sum := by decide
  have hdescent : baseEnd_4100348 < baseStart_4100348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100441 : List Nat := [1, 2, 1, 2, 2, 2, 1, 4, 1, 5, 2]
def baseStart_4100441 : Nat := 118140960795 + 4100441 * 2 ^ 59
def prefixEnd_4100441 : Nat := 4983230072969 + 3 ^ 40 * 4100441 * 2
def baseEnd_4100441 : Nat := 2105497128402696739429921

theorem tailTrace_4100441 : CollatzResearch.WordTrace tailWord_4100441 prefixEnd_4100441 2105497128402696739429921 := by
  unfold tailWord_4100441
  simp only [CollatzResearch.WordTrace]
  refine ⟨149555369737810031414213177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99703579825206687609475451 149555369737810031414213177)
  ·
    refine ⟨112166527303357523560659883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149555369737810031414213177 112166527303357523560659883)
    ·
      refine ⟨168249790955036285340989825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112166527303357523560659883 168249790955036285340989825)
      ·
        refine ⟨126187343216277214005742369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168249790955036285340989825 126187343216277214005742369)
        ·
          refine ⟨94640507412207910504306777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126187343216277214005742369 94640507412207910504306777)
          ·
            refine ⟨70980380559155932878230083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94640507412207910504306777 70980380559155932878230083)
            ·
              refine ⟨106470570838733899317345125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70980380559155932878230083 106470570838733899317345125)
              ·
                refine ⟨19963232032262606122002211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106470570838733899317345125 19963232032262606122002211)
                ·
                  refine ⟨29944848048393909183003317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19963232032262606122002211 29944848048393909183003317)
                  ·
                    refine ⟨2807329504536928985906561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29944848048393909183003317 2807329504536928985906561)
                    ·
                      refine ⟨2105497128402696739429921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2807329504536928985906561 2105497128402696739429921)
                      ·
                        rfl

theorem cell23_4100441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 5, 2].length) (baseStart_4100441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4100441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4100441 prefixEnd_4100441 := by exact prefixLift 4100441
  have htrace : WordTrace (prefixWord ++ tailWord_4100441) baseStart_4100441 baseEnd_4100441 := by
    simpa [prefixWord, tailWord_4100441, baseEnd_4100441] using wordTrace_append hprefix tailTrace_4100441
  have hstable : (prefixWord ++ tailWord_4100441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100441).length < 2 ^ (prefixWord ++ tailWord_4100441).sum := by decide
  have hdescent : baseEnd_4100441 < baseStart_4100441 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100446 : List Nat := [4, 4, 2, 1, 2, 1, 1, 1, 2, 5]
def baseStart_4100446 : Nat := 118140960795 + 4100446 * 2 ^ 59
def prefixEnd_4100446 : Nat := 4983230072969 + 3 ^ 40 * 4100446 * 2
def baseEnd_4100446 : Nat := 701833231935323073289133

theorem tailTrace_4100446 : CollatzResearch.WordTrace tailWord_4100446 prefixEnd_4100446 701833231935323073289133 := by
  unfold tailWord_4100446
  simp only [CollatzResearch.WordTrace]
  refine ⟨18694444012848989658518149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99703701401861278178763461 18694444012848989658518149)
  ·
    refine ⟨3505208252409185560972153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18694444012848989658518149 3505208252409185560972153)
    ·
      refine ⟨2628906189306889170729115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3505208252409185560972153 2628906189306889170729115)
      ·
        refine ⟨3943359283960333756093673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2628906189306889170729115 3943359283960333756093673)
        ·
          refine ⟨2957519462970250317070255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3943359283960333756093673 2957519462970250317070255)
          ·
            refine ⟨4436279194455375475605383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2957519462970250317070255 4436279194455375475605383)
            ·
              refine ⟨6654418791683063213408075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4436279194455375475605383 6654418791683063213408075)
              ·
                refine ⟨9981628187524594820112113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6654418791683063213408075 9981628187524594820112113)
                ·
                  refine ⟨7486221140643446115084085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9981628187524594820112113 7486221140643446115084085)
                  ·
                    refine ⟨701833231935323073289133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7486221140643446115084085 701833231935323073289133)
                    ·
                      rfl

theorem cell23_4100446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_4100446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4100446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4100446 prefixEnd_4100446 := by exact prefixLift 4100446
  have htrace : WordTrace (prefixWord ++ tailWord_4100446) baseStart_4100446 baseEnd_4100446 := by
    simpa [prefixWord, tailWord_4100446, baseEnd_4100446] using wordTrace_append hprefix tailTrace_4100446
  have hstable : (prefixWord ++ tailWord_4100446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100446).length < 2 ^ (prefixWord ++ tailWord_4100446).sum := by decide
  have hdescent : baseEnd_4100446 < baseStart_4100446 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100451 : List Nat := [1, 1, 1, 5, 2, 1, 2, 4, 1, 5]
def baseStart_4100451 : Nat := 118140960795 + 4100451 * 2 ^ 59
def prefixEnd_4100451 : Nat := 4983230072969 + 3 ^ 40 * 4100451 * 2
def baseEnd_4100451 : Nat := 701834087736413900101625

theorem tailTrace_4100451 : CollatzResearch.WordTrace tailWord_4100451 prefixEnd_4100451 701834087736413900101625 := by
  unfold tailWord_4100451
  simp only [CollatzResearch.WordTrace]
  refine ⟨149555734467773803122077207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99703822978515868748051471 149555734467773803122077207)
  ·
    refine ⟨224333601701660704683115811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149555734467773803122077207 224333601701660704683115811)
    ·
      refine ⟨336500402552491057024673717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224333601701660704683115811 336500402552491057024673717)
      ·
        refine ⟨31546912739296036596063161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 336500402552491057024673717 31546912739296036596063161)
        ·
          refine ⟨23660184554472027447047371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31546912739296036596063161 23660184554472027447047371)
          ·
            refine ⟨35490276831708041170571057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23660184554472027447047371 35490276831708041170571057)
            ·
              refine ⟨26617707623781030877928293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35490276831708041170571057 26617707623781030877928293)
              ·
                refine ⟨4990820179458943289611555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26617707623781030877928293 4990820179458943289611555)
                ·
                  refine ⟨7486230269188414934417333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4990820179458943289611555 7486230269188414934417333)
                  ·
                    refine ⟨701834087736413900101625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7486230269188414934417333 701834087736413900101625)
                    ·
                      rfl

theorem cell23_4100451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 4, 1, 5].length) (baseStart_4100451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4100451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4100451 prefixEnd_4100451 := by exact prefixLift 4100451
  have htrace : WordTrace (prefixWord ++ tailWord_4100451) baseStart_4100451 baseEnd_4100451 := by
    simpa [prefixWord, tailWord_4100451, baseEnd_4100451] using wordTrace_append hprefix tailTrace_4100451
  have hstable : (prefixWord ++ tailWord_4100451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100451).length < 2 ^ (prefixWord ++ tailWord_4100451).sum := by decide
  have hdescent : baseEnd_4100451 < baseStart_4100451 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100491 : List Nat := [1, 1, 1, 1, 4, 5, 1, 2, 1, 1, 5]
def baseStart_4100491 : Nat := 118140960795 + 4100491 * 2 ^ 59
def prefixEnd_4100491 : Nat := 4983230072969 + 3 ^ 40 * 4100491 * 2
def baseEnd_4100491 : Nat := 2105522802435421543804691

theorem tailTrace_4100491 : CollatzResearch.WordTrace tailWord_4100491 prefixEnd_4100491 2105522802435421543804691 := by
  unfold tailWord_4100491
  simp only [CollatzResearch.WordTrace]
  refine ⟨149557193387628889953533327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99704795591752593302355551 149557193387628889953533327)
  ·
    refine ⟨224335790081443334930299991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149557193387628889953533327 224335790081443334930299991)
    ·
      refine ⟨336503685122165002395449987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224335790081443334930299991 336503685122165002395449987)
      ·
        refine ⟨504755527683247503593174981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336503685122165002395449987 504755527683247503593174981)
        ·
          refine ⟨94641661440608906923720309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 504755527683247503593174981 94641661440608906923720309)
          ·
            refine ⟨8872655760057085024098779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94641661440608906923720309 8872655760057085024098779)
            ·
              refine ⟨13308983640085627536148169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8872655760057085024098779 13308983640085627536148169)
              ·
                refine ⟨9981737730064220652111127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13308983640085627536148169 9981737730064220652111127)
                ·
                  refine ⟨14972606595096330978166691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9981737730064220652111127 14972606595096330978166691)
                  ·
                    refine ⟨22458909892644496467250037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14972606595096330978166691 22458909892644496467250037)
                    ·
                      refine ⟨2105522802435421543804691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22458909892644496467250037 2105522802435421543804691)
                      ·
                        rfl

theorem cell23_4100491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 2, 1, 1, 5].length) (baseStart_4100491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4100491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4100491 prefixEnd_4100491 := by exact prefixLift 4100491
  have htrace : WordTrace (prefixWord ++ tailWord_4100491) baseStart_4100491 baseEnd_4100491 := by
    simpa [prefixWord, tailWord_4100491, baseEnd_4100491] using wordTrace_append hprefix tailTrace_4100491
  have hstable : (prefixWord ++ tailWord_4100491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100491).length < 2 ^ (prefixWord ++ tailWord_4100491).sum := by decide
  have hdescent : baseEnd_4100491 < baseStart_4100491 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100521 : List Nat := [1, 2, 1, 1, 1, 1, 3, 6, 1, 3, 3]
def baseStart_4100521 : Nat := 118140960795 + 4100521 * 2 ^ 59
def prefixEnd_4100521 : Nat := 4983230072969 + 3 ^ 40 * 4100521 * 2
def baseEnd_4100521 : Nat := 2105538206855056426429553

theorem tailTrace_4100521 : CollatzResearch.WordTrace tailWord_4100521 prefixEnd_4100521 2105538206855056426429553 := by
  unfold tailWord_4100521
  simp only [CollatzResearch.WordTrace]
  refine ⟨149558287577520205077125417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99705525051680136718083611 149558287577520205077125417)
  ·
    refine ⟨112168715683140153807844063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149558287577520205077125417 112168715683140153807844063)
    ·
      refine ⟨168253073524710230711766095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112168715683140153807844063 168253073524710230711766095)
      ·
        refine ⟨252379610287065346067649143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168253073524710230711766095 252379610287065346067649143)
        ·
          refine ⟨378569415430598019101473715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252379610287065346067649143 378569415430598019101473715)
          ·
            refine ⟨567854123145897028652210573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378569415430598019101473715 567854123145897028652210573)
            ·
              refine ⟨212945296179711385744578965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 567854123145897028652210573 212945296179711385744578965)
              ·
                refine ⟨9981810758423971206777139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 212945296179711385744578965 9981810758423971206777139)
                ·
                  refine ⟨14972716137635956810165709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9981810758423971206777139 14972716137635956810165709)
                  ·
                    refine ⟨5614768551613483803812141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14972716137635956810165709 5614768551613483803812141)
                    ·
                      refine ⟨2105538206855056426429553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5614768551613483803812141 2105538206855056426429553)
                      ·
                        rfl

theorem cell23_4100521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 6, 1, 3, 3].length) (baseStart_4100521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4100521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4100521 prefixEnd_4100521 := by exact prefixLift 4100521
  have htrace : WordTrace (prefixWord ++ tailWord_4100521) baseStart_4100521 baseEnd_4100521 := by
    simpa [prefixWord, tailWord_4100521, baseEnd_4100521] using wordTrace_append hprefix tailTrace_4100521
  have hstable : (prefixWord ++ tailWord_4100521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100521).length < 2 ^ (prefixWord ++ tailWord_4100521).sum := by decide
  have hdescent : baseEnd_4100521 < baseStart_4100521 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100524 : List Nat := [2, 2, 1, 1, 1, 1, 3, 2, 1, 9]
def baseStart_4100524 : Nat := 118140960795 + 4100524 * 2 ^ 59
def prefixEnd_4100524 : Nat := 4983230072969 + 3 ^ 40 * 4100524 * 2
def baseEnd_4100524 : Nat := 701846582432339971564013

theorem tailTrace_4100524 : CollatzResearch.WordTrace tailWord_4100524 prefixEnd_4100524 701846582432339971564013 := by
  unfold tailWord_4100524
  simp only [CollatzResearch.WordTrace]
  refine ⟨74779198498254668294742313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99705597997672891059656417 74779198498254668294742313)
  ·
    refine ⟨56084398873691001221056735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74779198498254668294742313 56084398873691001221056735)
    ·
      refine ⟨84126598310536501831585103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56084398873691001221056735 84126598310536501831585103)
      ·
        refine ⟨126189897465804752747377655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84126598310536501831585103 126189897465804752747377655)
        ·
          refine ⟨189284846198707129121066483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126189897465804752747377655 189284846198707129121066483)
          ·
            refine ⟨283927269298060693681599725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189284846198707129121066483 283927269298060693681599725)
            ·
              refine ⟨106472725986772760130599897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 283927269298060693681599725 106472725986772760130599897)
              ·
                refine ⟨79854544490079570097949923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106472725986772760130599897 79854544490079570097949923)
                ·
                  refine ⟨119781816735119355146924885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79854544490079570097949923 119781816735119355146924885)
                  ·
                    refine ⟨701846582432339971564013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 119781816735119355146924885 701846582432339971564013)
                    ·
                      rfl

theorem cell23_4100524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 9].length) (baseStart_4100524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4100524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4100524 prefixEnd_4100524 := by exact prefixLift 4100524
  have htrace : WordTrace (prefixWord ++ tailWord_4100524) baseStart_4100524 baseEnd_4100524 := by
    simpa [prefixWord, tailWord_4100524, baseEnd_4100524] using wordTrace_append hprefix tailTrace_4100524
  have hstable : (prefixWord ++ tailWord_4100524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100524).length < 2 ^ (prefixWord ++ tailWord_4100524).sum := by decide
  have hdescent : baseEnd_4100524 < baseStart_4100524 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100525 : List Nat := [1, 5, 2, 2, 2, 1, 2, 1, 1, 1, 5]
def baseStart_4100525 : Nat := 118140960795 + 4100525 * 2 ^ 59
def prefixEnd_4100525 : Nat := 4983230072969 + 3 ^ 40 * 4100525 * 2
def baseEnd_4100525 : Nat := 2105540260777674410779535

theorem tailTrace_4100525 : CollatzResearch.WordTrace tailWord_4100525 prefixEnd_4100525 2105540260777674410779535 := by
  unfold tailWord_4100525
  simp only [CollatzResearch.WordTrace]
  refine ⟨149558433469505713760271029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99705622313003809173514019 149558433469505713760271029)
  ·
    refine ⟨14021103137766160665025409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 149558433469505713760271029 14021103137766160665025409)
    ·
      refine ⟨10515827353324620498769057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14021103137766160665025409 10515827353324620498769057)
      ·
        refine ⟨7886870514993465374076793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10515827353324620498769057 7886870514993465374076793)
        ·
          refine ⟨5915152886245099030557595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7886870514993465374076793 5915152886245099030557595)
          ·
            refine ⟨8872729329367648545836393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5915152886245099030557595 8872729329367648545836393)
            ·
              refine ⟨6654546997025736409377295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8872729329367648545836393 6654546997025736409377295)
              ·
                refine ⟨9981820495538604614065943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6654546997025736409377295 9981820495538604614065943)
                ·
                  refine ⟨14972730743307906921098915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9981820495538604614065943 14972730743307906921098915)
                  ·
                    refine ⟨22459096114961860381648373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14972730743307906921098915 22459096114961860381648373)
                    ·
                      refine ⟨2105540260777674410779535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22459096114961860381648373 2105540260777674410779535)
                      ·
                        rfl

theorem cell23_4100525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_4100525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4100525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4100525 prefixEnd_4100525 := by exact prefixLift 4100525
  have htrace : WordTrace (prefixWord ++ tailWord_4100525) baseStart_4100525 baseEnd_4100525 := by
    simpa [prefixWord, tailWord_4100525, baseEnd_4100525] using wordTrace_append hprefix tailTrace_4100525
  have hstable : (prefixWord ++ tailWord_4100525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100525).length < 2 ^ (prefixWord ++ tailWord_4100525).sum := by decide
  have hdescent : baseEnd_4100525 < baseStart_4100525 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100565 : List Nat := [1, 3, 2, 3, 1, 3, 1, 1, 3, 3, 2]
def baseStart_4100565 : Nat := 118140960795 + 4100565 * 2 ^ 59
def prefixEnd_4100565 : Nat := 4983230072969 + 3 ^ 40 * 4100565 * 2
def baseEnd_4100565 : Nat := 2105560800003854254279351

theorem tailTrace_4100565 : CollatzResearch.WordTrace tailWord_4100565 prefixEnd_4100565 2105560800003854254279351 := by
  unfold tailWord_4100565
  simp only [CollatzResearch.WordTrace]
  refine ⟨149559892389360800591727149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99706594926240533727818099 149559892389360800591727149)
  ·
    refine ⟨56084959646010300221897681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149559892389360800591727149 56084959646010300221897681)
    ·
      refine ⟨42063719734507725166423261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56084959646010300221897681 42063719734507725166423261)
      ·
        refine ⟨15773894900440396937408723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42063719734507725166423261 15773894900440396937408723)
        ·
          refine ⟨23660842350660595406113085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15773894900440396937408723 23660842350660595406113085)
          ·
            refine ⟨8872815881497723277292407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23660842350660595406113085 8872815881497723277292407)
            ·
              refine ⟨13309223822246584915938611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8872815881497723277292407 13309223822246584915938611)
              ·
                refine ⟨19963835733369877373907917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13309223822246584915938611 19963835733369877373907917)
                ·
                  refine ⟨7486438400013704015215469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19963835733369877373907917 7486438400013704015215469)
                  ·
                    refine ⟨2807414400005139005705801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7486438400013704015215469 2807414400005139005705801)
                    ·
                      refine ⟨2105560800003854254279351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2807414400005139005705801 2105560800003854254279351)
                      ·
                        rfl

theorem cell23_4100565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 3, 3, 2].length) (baseStart_4100565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4100565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4100565 prefixEnd_4100565 := by exact prefixLift 4100565
  have htrace : WordTrace (prefixWord ++ tailWord_4100565) baseStart_4100565 baseEnd_4100565 := by
    simpa [prefixWord, tailWord_4100565, baseEnd_4100565] using wordTrace_append hprefix tailTrace_4100565
  have hstable : (prefixWord ++ tailWord_4100565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100565).length < 2 ^ (prefixWord ++ tailWord_4100565).sum := by decide
  have hdescent : baseEnd_4100565 < baseStart_4100565 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100591 : List Nat := [1, 1, 2, 1, 4, 1, 1, 4, 2, 2, 4]
def baseStart_4100591 : Nat := 118140960795 + 4100591 * 2 ^ 59
def prefixEnd_4100591 : Nat := 4983230072969 + 3 ^ 40 * 4100591 * 2
def baseEnd_4100591 : Nat := 2105574150500871152554231

theorem tailTrace_4100591 : CollatzResearch.WordTrace tailWord_4100591 prefixEnd_4100591 2105574150500871152554231 := by
  unfold tailWord_4100591
  simp only [CollatzResearch.WordTrace]
  refine ⟨149560840687266607032173627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99707227124844404688115751 149560840687266607032173627)
  ·
    refine ⟨224341261030899910548260441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149560840687266607032173627 224341261030899910548260441)
    ·
      refine ⟨168255945773174932911195331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224341261030899910548260441 168255945773174932911195331)
      ·
        refine ⟨252383918659762399366792997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168255945773174932911195331 252383918659762399366792997)
        ·
          refine ⟨47321984748705449881273687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 252383918659762399366792997 47321984748705449881273687)
          ·
            refine ⟨70982977123058174821910531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47321984748705449881273687 70982977123058174821910531)
            ·
              refine ⟨106474465684587262232865797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70982977123058174821910531 106474465684587262232865797)
              ·
                refine ⟨19963962315860111668662337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106474465684587262232865797 19963962315860111668662337)
                ·
                  refine ⟨14972971736895083751496753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19963962315860111668662337 14972971736895083751496753)
                  ·
                    refine ⟨11229728802671312813622565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14972971736895083751496753 11229728802671312813622565)
                    ·
                      refine ⟨2105574150500871152554231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11229728802671312813622565 2105574150500871152554231)
                      ·
                        rfl

theorem cell23_4100591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 2, 2, 4].length) (baseStart_4100591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4100591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4100591 prefixEnd_4100591 := by exact prefixLift 4100591
  have htrace : WordTrace (prefixWord ++ tailWord_4100591) baseStart_4100591 baseEnd_4100591 := by
    simpa [prefixWord, tailWord_4100591, baseEnd_4100591] using wordTrace_append hprefix tailTrace_4100591
  have hstable : (prefixWord ++ tailWord_4100591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100591).length < 2 ^ (prefixWord ++ tailWord_4100591).sum := by decide
  have hdescent : baseEnd_4100591 < baseStart_4100591 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100598 : List Nat := [5, 1, 1, 1, 2, 1, 1, 1, 1, 6, 3]
def baseStart_4100598 : Nat := 118140960795 + 4100598 * 2 ^ 59
def prefixEnd_4100598 : Nat := 4983230072969 + 3 ^ 40 * 4100598 * 2
def baseEnd_4100598 : Nat := 2105577744865452625166699

theorem tailTrace_4100598 : CollatzResearch.WordTrace tailWord_4100598 prefixEnd_4100598 2105577744865452625166699 := by
  unfold tailWord_4100598
  simp only [CollatzResearch.WordTrace]
  refine ⟨9347568499890077951729903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99707397332160831485118965 9347568499890077951729903)
  ·
    refine ⟨14021352749835116927594855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9347568499890077951729903 14021352749835116927594855)
    ·
      refine ⟨21032029124752675391392283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14021352749835116927594855 21032029124752675391392283)
      ·
        refine ⟨31548043687129013087088425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21032029124752675391392283 31548043687129013087088425)
        ·
          refine ⟨23661032765346759815316319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31548043687129013087088425 23661032765346759815316319)
          ·
            refine ⟨35491549148020139722974479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23661032765346759815316319 35491549148020139722974479)
            ·
              refine ⟨53237323722030209584461719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35491549148020139722974479 53237323722030209584461719)
              ·
                refine ⟨79855985583045314376692579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53237323722030209584461719 79855985583045314376692579)
                ·
                  refine ⟨119783978374567971565038869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79855985583045314376692579 119783978374567971565038869)
                  ·
                    refine ⟨5614873986307873667111197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 119783978374567971565038869 5614873986307873667111197)
                    ·
                      refine ⟨2105577744865452625166699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5614873986307873667111197 2105577744865452625166699)
                      ·
                        rfl

theorem cell23_4100598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 1, 6, 3].length) (baseStart_4100598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4100598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4100598 prefixEnd_4100598 := by exact prefixLift 4100598
  have htrace : WordTrace (prefixWord ++ tailWord_4100598) baseStart_4100598 baseEnd_4100598 := by
    simpa [prefixWord, tailWord_4100598, baseEnd_4100598] using wordTrace_append hprefix tailTrace_4100598
  have hstable : (prefixWord ++ tailWord_4100598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100598).length < 2 ^ (prefixWord ++ tailWord_4100598).sum := by decide
  have hdescent : baseEnd_4100598 < baseStart_4100598 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100612 : List Nat := [2, 3, 2, 3, 1, 2, 2, 1, 1, 4, 2]
def baseStart_4100612 : Nat := 118140960795 + 4100612 * 2 ^ 59
def prefixEnd_4100612 : Nat := 4983230072969 + 3 ^ 40 * 4100612 * 2
def baseEnd_4100612 : Nat := 2105584933594615570391635

theorem tailTrace_4100612 : CollatzResearch.WordTrace tailWord_4100612 prefixEnd_4100612 2105584933594615570391635 := by
  unfold tailWord_4100612
  simp only [CollatzResearch.WordTrace]
  refine ⟨74780803310095263809344045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99707737746793685079125393 74780803310095263809344045)
  ·
    refine ⟨28042801241285723928504017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74780803310095263809344045 28042801241285723928504017)
    ·
      refine ⟨21032100930964292946378013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28042801241285723928504017 21032100930964292946378013)
      ·
        refine ⟨7887037849111609854891755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21032100930964292946378013 7887037849111609854891755)
        ·
          refine ⟨11830556773667414782337633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7887037849111609854891755 11830556773667414782337633)
          ·
            refine ⟨8872917580250561086753225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11830556773667414782337633 8872917580250561086753225)
            ·
              refine ⟨6654688185187920815064919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8872917580250561086753225 6654688185187920815064919)
              ·
                refine ⟨9982032277781881222597379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6654688185187920815064919 9982032277781881222597379)
                ·
                  refine ⟨14973048416672821833896069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9982032277781881222597379 14973048416672821833896069)
                  ·
                    refine ⟨2807446578126154093855513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14973048416672821833896069 2807446578126154093855513)
                    ·
                      refine ⟨2105584933594615570391635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2807446578126154093855513 2105584933594615570391635)
                      ·
                        rfl

theorem cell23_4100612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_4100612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4100612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4100612 prefixEnd_4100612 := by exact prefixLift 4100612
  have htrace : WordTrace (prefixWord ++ tailWord_4100612) baseStart_4100612 baseEnd_4100612 := by
    simpa [prefixWord, tailWord_4100612, baseEnd_4100612] using wordTrace_append hprefix tailTrace_4100612
  have hstable : (prefixWord ++ tailWord_4100612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100612).length < 2 ^ (prefixWord ++ tailWord_4100612).sum := by decide
  have hdescent : baseEnd_4100612 < baseStart_4100612 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100668 : List Nat := [2, 2, 2, 2, 3, 1, 1, 2, 1, 3, 4]
def baseStart_4100668 : Nat := 118140960795 + 4100668 * 2 ^ 59
def prefixEnd_4100668 : Nat := 4983230072969 + 3 ^ 40 * 4100668 * 2
def baseEnd_4100668 : Nat := 2105613688511267351291377

theorem tailTrace_4100668 : CollatzResearch.WordTrace tailWord_4100668 prefixEnd_4100668 2105613688511267351291377 := by
  unfold tailWord_4100668
  simp only [CollatzResearch.WordTrace]
  refine ⟨74781824553993824591363329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99709099405325099455151105 74781824553993824591363329)
  ·
    refine ⟨56086368415495368443522497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74781824553993824591363329 56086368415495368443522497)
    ·
      refine ⟨42064776311621526332641873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56086368415495368443522497 42064776311621526332641873)
      ·
        refine ⟨31548582233716144749481405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42064776311621526332641873 31548582233716144749481405)
        ·
          refine ⟨11830718337643554281055527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31548582233716144749481405 11830718337643554281055527)
          ·
            refine ⟨17746077506465331421583291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11830718337643554281055527 17746077506465331421583291)
            ·
              refine ⟨26619116259697997132374937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17746077506465331421583291 26619116259697997132374937)
              ·
                refine ⟨19964337194773497849281203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26619116259697997132374937 19964337194773497849281203)
                ·
                  refine ⟨29946505792160246773921805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19964337194773497849281203 29946505792160246773921805)
                  ·
                    refine ⟨11229939672060092540220677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29946505792160246773921805 11229939672060092540220677)
                    ·
                      refine ⟨2105613688511267351291377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11229939672060092540220677 2105613688511267351291377)
                      ·
                        rfl

theorem cell23_4100668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_4100668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4100668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4100668 prefixEnd_4100668 := by exact prefixLift 4100668
  have htrace : WordTrace (prefixWord ++ tailWord_4100668) baseStart_4100668 baseEnd_4100668 := by
    simpa [prefixWord, tailWord_4100668, baseEnd_4100668] using wordTrace_append hprefix tailTrace_4100668
  have hstable : (prefixWord ++ tailWord_4100668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100668).length < 2 ^ (prefixWord ++ tailWord_4100668).sum := by decide
  have hdescent : baseEnd_4100668 < baseStart_4100668 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100685 : List Nat := [1, 6, 1, 1, 2, 1, 2, 1, 1, 3, 4]
def baseStart_4100685 : Nat := 118140960795 + 4100685 * 2 ^ 59
def prefixEnd_4100685 : Nat := 4983230072969 + 3 ^ 40 * 4100685 * 2
def baseEnd_4100685 : Nat := 2105622417682393784778799

theorem tailTrace_4100685 : CollatzResearch.WordTrace tailWord_4100685 prefixEnd_4100685 2105622417682393784778799 := by
  unfold tailWord_4100685
  simp only [CollatzResearch.WordTrace]
  refine ⟨149564269148926061086095509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99709512765950707390730339 149564269148926061086095509)
  ·
    refine ⟨7010825116355909113410727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 149564269148926061086095509 7010825116355909113410727)
    ·
      refine ⟨10516237674533863670116091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7010825116355909113410727 10516237674533863670116091)
      ·
        refine ⟨15774356511800795505174137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10516237674533863670116091 15774356511800795505174137)
        ·
          refine ⟨11830767383850596628880603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15774356511800795505174137 11830767383850596628880603)
          ·
            refine ⟨17746151075775894943320905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11830767383850596628880603 17746151075775894943320905)
            ·
              refine ⟨13309613306831921207490679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17746151075775894943320905 13309613306831921207490679)
              ·
                refine ⟨19964419960247881811236019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13309613306831921207490679 19964419960247881811236019)
                ·
                  refine ⟨29946629940371822716854029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19964419960247881811236019 29946629940371822716854029)
                  ·
                    refine ⟨11229986227639433518820261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29946629940371822716854029 11229986227639433518820261)
                    ·
                      refine ⟨2105622417682393784778799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11229986227639433518820261 2105622417682393784778799)
                      ·
                        rfl

theorem cell23_4100685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_4100685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4100685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4100685 prefixEnd_4100685 := by exact prefixLift 4100685
  have htrace : WordTrace (prefixWord ++ tailWord_4100685) baseStart_4100685 baseEnd_4100685 := by
    simpa [prefixWord, tailWord_4100685, baseEnd_4100685] using wordTrace_append hprefix tailTrace_4100685
  have hstable : (prefixWord ++ tailWord_4100685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100685).length < 2 ^ (prefixWord ++ tailWord_4100685).sum := by decide
  have hdescent : baseEnd_4100685 < baseStart_4100685 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100705 : List Nat := [1, 2, 3, 1, 1, 5, 1, 2, 2, 2, 3]
def baseStart_4100705 : Nat := 118140960795 + 4100705 * 2 ^ 59
def prefixEnd_4100705 : Nat := 4983230072969 + 3 ^ 40 * 4100705 * 2
def baseEnd_4100705 : Nat := 2105632687295483706528707

theorem tailTrace_4100705 : CollatzResearch.WordTrace tailWord_4100705 prefixEnd_4100705 2105632687295483706528707 := by
  unfold tailWord_4100705
  simp only [CollatzResearch.WordTrace]
  refine ⟨149564998608853604501823569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99709999072569069667882379 149564998608853604501823569)
  ·
    refine ⟨112173748956640203376367677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149564998608853604501823569 112173748956640203376367677)
    ·
      refine ⟨42065155858740076266137879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112173748956640203376367677 42065155858740076266137879)
      ·
        refine ⟨63097733788110114399206819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42065155858740076266137879 63097733788110114399206819)
        ·
          refine ⟨94646600682165171598810229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63097733788110114399206819 94646600682165171598810229)
          ·
            refine ⟨8873118813952984837388459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94646600682165171598810229 8873118813952984837388459)
            ·
              refine ⟨13309678220929477256082689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8873118813952984837388459 13309678220929477256082689)
              ·
                refine ⟨9982258665697107942062017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13309678220929477256082689 9982258665697107942062017)
                ·
                  refine ⟨7486693999272830956546513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9982258665697107942062017 7486693999272830956546513)
                  ·
                    refine ⟨5615020499454623217409885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7486693999272830956546513 5615020499454623217409885)
                    ·
                      refine ⟨2105632687295483706528707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5615020499454623217409885 2105632687295483706528707)
                      ·
                        rfl

theorem cell23_4100705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 2, 2, 2, 3].length) (baseStart_4100705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4100705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4100705 prefixEnd_4100705 := by exact prefixLift 4100705
  have htrace : WordTrace (prefixWord ++ tailWord_4100705) baseStart_4100705 baseEnd_4100705 := by
    simpa [prefixWord, tailWord_4100705, baseEnd_4100705] using wordTrace_append hprefix tailTrace_4100705
  have hstable : (prefixWord ++ tailWord_4100705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100705).length < 2 ^ (prefixWord ++ tailWord_4100705).sum := by decide
  have hdescent : baseEnd_4100705 < baseStart_4100705 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100708 : List Nat := [2, 3, 1, 1, 2, 2, 2, 4, 6]
def baseStart_4100708 : Nat := 118140960795 + 4100708 * 2 ^ 59
def prefixEnd_4100708 : Nat := 4983230072969 + 3 ^ 40 * 4100708 * 2
def baseEnd_4100708 : Nat := 233959358637494132754577

theorem tailTrace_4100708 : CollatzResearch.WordTrace tailWord_4100708 prefixEnd_4100708 233959358637494132754577 := by
  unfold tailWord_4100708
  simp only [CollatzResearch.WordTrace]
  refine ⟨74782554013921368007091389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99710072018561824009455185 74782554013921368007091389)
  ·
    refine ⟨28043457755220513002659271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74782554013921368007091389 28043457755220513002659271)
    ·
      refine ⟨42065186632830769503988907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28043457755220513002659271 42065186632830769503988907)
      ·
        refine ⟨63097779949246154255983361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42065186632830769503988907 63097779949246154255983361)
        ·
          refine ⟨47323334961934615691987521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63097779949246154255983361 47323334961934615691987521)
          ·
            refine ⟨35492501221450961768990641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47323334961934615691987521 35492501221450961768990641)
            ·
              refine ⟨26619375916088221326742981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35492501221450961768990641 26619375916088221326742981)
              ·
                refine ⟨4991132984266541498764309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26619375916088221326742981 4991132984266541498764309)
                ·
                  refine ⟨233959358637494132754577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4991132984266541498764309 233959358637494132754577)
                  ·
                    rfl

theorem cell23_4100708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 4, 6].length) (baseStart_4100708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4100708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4100708 prefixEnd_4100708 := by exact prefixLift 4100708
  have htrace : WordTrace (prefixWord ++ tailWord_4100708) baseStart_4100708 baseEnd_4100708 := by
    simpa [prefixWord, tailWord_4100708, baseEnd_4100708] using wordTrace_append hprefix tailTrace_4100708
  have hstable : (prefixWord ++ tailWord_4100708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100708).length < 2 ^ (prefixWord ++ tailWord_4100708).sum := by decide
  have hdescent : baseEnd_4100708 < baseStart_4100708 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100721 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 1, 11]
def baseStart_4100721 : Nat := 118140960795 + 4100721 * 2 ^ 59
def prefixEnd_4100721 : Nat := 4983230072969 + 3 ^ 40 * 4100721 * 2
def baseEnd_4100721 : Nat := 701880300995318547976211

theorem tailTrace_4100721 : CollatzResearch.WordTrace tailWord_4100721 prefixEnd_4100721 701880300995318547976211 := by
  unfold tailWord_4100721
  simp only [CollatzResearch.WordTrace]
  refine ⟨149565582176795639234406017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99710388117863759489604011 149565582176795639234406017)
  ·
    refine ⟨112174186632596729425804513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149565582176795639234406017 112174186632596729425804513)
    ·
      refine ⟨84130639974447547069353385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112174186632596729425804513 84130639974447547069353385)
      ·
        refine ⟨63097979980835660302015039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84130639974447547069353385 63097979980835660302015039)
        ·
          refine ⟨94646969971253490453022559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63097979980835660302015039 94646969971253490453022559)
          ·
            refine ⟨141970454956880235679533839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94646969971253490453022559 141970454956880235679533839)
            ·
              refine ⟨212955682435320353519300759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141970454956880235679533839 212955682435320353519300759)
              ·
                refine ⟨319433523652980530278951139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212955682435320353519300759 319433523652980530278951139)
                ·
                  refine ⟨479150285479470795418426709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 319433523652980530278951139 479150285479470795418426709)
                  ·
                    refine ⟨701880300995318547976211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 479150285479470795418426709 701880300995318547976211)
                    ·
                      rfl

theorem cell23_4100721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 11].length) (baseStart_4100721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4100721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4100721 prefixEnd_4100721 := by exact prefixLift 4100721
  have htrace : WordTrace (prefixWord ++ tailWord_4100721) baseStart_4100721 baseEnd_4100721 := by
    simpa [prefixWord, tailWord_4100721, baseEnd_4100721] using wordTrace_append hprefix tailTrace_4100721
  have hstable : (prefixWord ++ tailWord_4100721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100721).length < 2 ^ (prefixWord ++ tailWord_4100721).sum := by decide
  have hdescent : baseEnd_4100721 < baseStart_4100721 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100731 : List Nat := [1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 7]
def baseStart_4100731 : Nat := 118140960795 + 4100731 * 2 ^ 59
def prefixEnd_4100731 : Nat := 4983230072969 + 3 ^ 40 * 4100731 * 2
def baseEnd_4100731 : Nat := 2105646037792500604803587

theorem tailTrace_4100731 : CollatzResearch.WordTrace tailWord_4100731 prefixEnd_4100731 2105646037792500604803587 := by
  unfold tailWord_4100731
  simp only [CollatzResearch.WordTrace]
  refine ⟨149565946906759410942270047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99710631271172940628180031 149565946906759410942270047)
  ·
    refine ⟨224348920360139116413405071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149565946906759410942270047 224348920360139116413405071)
    ·
      refine ⟨336523380540208674620107607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224348920360139116413405071 336523380540208674620107607)
      ·
        refine ⟨504785070810313011930161411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336523380540208674620107607 504785070810313011930161411)
        ·
          refine ⟨757177606215469517895242117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 504785070810313011930161411 757177606215469517895242117)
          ·
            refine ⟨141970801165400534605357897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 757177606215469517895242117 141970801165400534605357897)
            ·
              refine ⟨106478100874050400954018423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141970801165400534605357897 106478100874050400954018423)
              ·
                refine ⟨159717151311075601431027635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106478100874050400954018423 159717151311075601431027635)
                ·
                  refine ⟨239575726966613402146541453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 159717151311075601431027635 239575726966613402146541453)
                  ·
                    refine ⟨89840897612480025804953045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 239575726966613402146541453 89840897612480025804953045)
                    ·
                      refine ⟨2105646037792500604803587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 89840897612480025804953045 2105646037792500604803587)
                      ·
                        rfl

theorem cell23_4100731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 7].length) (baseStart_4100731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4100731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4100731 prefixEnd_4100731 := by exact prefixLift 4100731
  have htrace : WordTrace (prefixWord ++ tailWord_4100731) baseStart_4100731 baseEnd_4100731 := by
    simpa [prefixWord, tailWord_4100731, baseEnd_4100731] using wordTrace_append hprefix tailTrace_4100731
  have hstable : (prefixWord ++ tailWord_4100731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100731).length < 2 ^ (prefixWord ++ tailWord_4100731).sum := by decide
  have hdescent : baseEnd_4100731 < baseStart_4100731 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100806 : List Nat := [6, 1, 2, 1, 2, 1, 1, 3, 1, 5]
def baseStart_4100806 : Nat := 118140960795 + 4100806 * 2 ^ 59
def prefixEnd_4100806 : Nat := 4983230072969 + 3 ^ 40 * 4100806 * 2
def baseEnd_4100806 : Nat := 701894849613862603788581

theorem tailTrace_4100806 : CollatzResearch.WordTrace tailWord_4100806 prefixEnd_4100806 701894849613862603788581 := by
  unfold tailWord_4100806
  simp only [CollatzResearch.WordTrace]
  refine ⟨4674021324421490585976571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 99712454920991799167500181 4674021324421490585976571)
  ·
    refine ⟨7011031986632235878964857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4674021324421490585976571 7011031986632235878964857)
    ·
      refine ⟨5258273989974176909223643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7011031986632235878964857 5258273989974176909223643)
      ·
        refine ⟨7887410984961265363835465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5258273989974176909223643 7887410984961265363835465)
        ·
          refine ⟨5915558238720949022876599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7887410984961265363835465 5915558238720949022876599)
          ·
            refine ⟨8873337358081423534314899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5915558238720949022876599 8873337358081423534314899)
            ·
              refine ⟨13310006037122135301472349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8873337358081423534314899 13310006037122135301472349)
              ·
                refine ⟨4991252263920800738052131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13310006037122135301472349 4991252263920800738052131)
                ·
                  refine ⟨7486878395881201107078197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4991252263920800738052131 7486878395881201107078197)
                  ·
                    refine ⟨701894849613862603788581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7486878395881201107078197 701894849613862603788581)
                    ·
                      rfl

theorem cell23_4100806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_4100806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4100806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4100806 prefixEnd_4100806 := by exact prefixLift 4100806
  have htrace : WordTrace (prefixWord ++ tailWord_4100806) baseStart_4100806 baseEnd_4100806 := by
    simpa [prefixWord, tailWord_4100806, baseEnd_4100806] using wordTrace_append hprefix tailTrace_4100806
  have hstable : (prefixWord ++ tailWord_4100806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100806).length < 2 ^ (prefixWord ++ tailWord_4100806).sum := by decide
  have hdescent : baseEnd_4100806 < baseStart_4100806 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100858 : List Nat := [3, 1, 1, 1, 1, 3, 2, 2, 1, 8]
def baseStart_4100858 : Nat := 118140960795 + 4100858 * 2 ^ 59
def prefixEnd_4100858 : Nat := 4983230072969 + 3 ^ 40 * 4100858 * 2
def baseEnd_4100858 : Nat := 701903749945207202638501

theorem tailTrace_4100858 : CollatzResearch.WordTrace tailWord_4100858 prefixEnd_4100858 701903749945207202638501 := by
  unfold tailWord_4100858
  simp only [CollatzResearch.WordTrace]
  refine ⟨37392644744324827908035807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99713719318199541088095485 37392644744324827908035807)
  ·
    refine ⟨56088967116487241862053711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37392644744324827908035807 56088967116487241862053711)
    ·
      refine ⟨84133450674730862793080567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56088967116487241862053711 84133450674730862793080567)
      ·
        refine ⟨126200176012096294189620851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84133450674730862793080567 126200176012096294189620851)
        ·
          refine ⟨189300264018144441284431277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126200176012096294189620851 189300264018144441284431277)
          ·
            refine ⟨70987599006804165481661729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189300264018144441284431277 70987599006804165481661729)
            ·
              refine ⟨53240699255103124111246297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70987599006804165481661729 53240699255103124111246297)
              ·
                refine ⟨39930524441327343083434723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53240699255103124111246297 39930524441327343083434723)
                ·
                  refine ⟨59895786661991014625152085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39930524441327343083434723 59895786661991014625152085)
                  ·
                    refine ⟨701903749945207202638501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 59895786661991014625152085 701903749945207202638501)
                    ·
                      rfl

theorem cell23_4100858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 1, 8].length) (baseStart_4100858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4100858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4100858 prefixEnd_4100858 := by exact prefixLift 4100858
  have htrace : WordTrace (prefixWord ++ tailWord_4100858) baseStart_4100858 baseEnd_4100858 := by
    simpa [prefixWord, tailWord_4100858, baseEnd_4100858] using wordTrace_append hprefix tailTrace_4100858
  have hstable : (prefixWord ++ tailWord_4100858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100858).length < 2 ^ (prefixWord ++ tailWord_4100858).sum := by decide
  have hdescent : baseEnd_4100858 < baseStart_4100858 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100885 : List Nat := [1, 3, 2, 1, 2, 2, 2, 1, 2, 4, 3]
def baseStart_4100885 : Nat := 118140960795 + 4100885 * 2 ^ 59
def prefixEnd_4100885 : Nat := 4983230072969 + 3 ^ 40 * 4100885 * 2
def baseEnd_4100885 : Nat := 2105725113813293002277879

theorem tailTrace_4100885 : CollatzResearch.WordTrace tailWord_4100885 prefixEnd_4100885 2105725113813293002277879 := by
  unfold tailWord_4100885
  simp only [CollatzResearch.WordTrace]
  refine ⟨149571563748201495243376109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99714375832134330162250739 149571563748201495243376109)
  ·
    refine ⟨56089336405575560716266041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149571563748201495243376109 56089336405575560716266041)
    ·
      refine ⟨42067002304181670537199531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56089336405575560716266041 42067002304181670537199531)
      ·
        refine ⟨63100503456272505805799297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42067002304181670537199531 63100503456272505805799297)
        ·
          refine ⟨47325377592204379354349473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63100503456272505805799297 47325377592204379354349473)
          ·
            refine ⟨35494033194153284515762105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47325377592204379354349473 35494033194153284515762105)
            ·
              refine ⟨26620524895614963386821579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35494033194153284515762105 26620524895614963386821579)
              ·
                refine ⟨39930787343422445080232369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26620524895614963386821579 39930787343422445080232369)
                ·
                  refine ⟨29948090507566833810174277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39930787343422445080232369 29948090507566833810174277)
                  ·
                    refine ⟨5615266970168781339407677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29948090507566833810174277 5615266970168781339407677)
                    ·
                      refine ⟨2105725113813293002277879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5615266970168781339407677 2105725113813293002277879)
                      ·
                        rfl

theorem cell23_4100885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 4, 3].length) (baseStart_4100885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4100885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4100885 prefixEnd_4100885 := by exact prefixLift 4100885
  have htrace : WordTrace (prefixWord ++ tailWord_4100885) baseStart_4100885 baseEnd_4100885 := by
    simpa [prefixWord, tailWord_4100885, baseEnd_4100885] using wordTrace_append hprefix tailTrace_4100885
  have hstable : (prefixWord ++ tailWord_4100885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100885).length < 2 ^ (prefixWord ++ tailWord_4100885).sum := by decide
  have hdescent : baseEnd_4100885 < baseStart_4100885 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100916 : List Nat := [2, 5, 1, 1, 3, 1, 1, 2, 1, 4, 2]
def baseStart_4100916 : Nat := 118140960795 + 4100916 * 2 ^ 59
def prefixEnd_4100916 : Nat := 4983230072969 + 3 ^ 40 * 4100916 * 2
def baseEnd_4100916 : Nat := 2105741031713582380990237

theorem tailTrace_4100916 : CollatzResearch.WordTrace tailWord_4100916 prefixEnd_4100916 2105741031713582380990237 := by
  unfold tailWord_4100916
  simp only [CollatzResearch.WordTrace]
  refine ⟨74786347205544593768877301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99715129607392791691836401 74786347205544593768877301)
  ·
    refine ⟨7011220050519805665832247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74786347205544593768877301 7011220050519805665832247)
    ·
      refine ⟨10516830075779708498748371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7011220050519805665832247 10516830075779708498748371)
      ·
        refine ⟨15775245113669562748122557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10516830075779708498748371 15775245113669562748122557)
        ·
          refine ⟨5915716917626086030545959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15775245113669562748122557 5915716917626086030545959)
          ·
            refine ⟨8873575376439129045818939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5915716917626086030545959 8873575376439129045818939)
            ·
              refine ⟨13310363064658693568728409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8873575376439129045818939 13310363064658693568728409)
              ·
                refine ⟨9982772298494020176546307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13310363064658693568728409 9982772298494020176546307)
                ·
                  refine ⟨14974158447741030264819461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9982772298494020176546307 14974158447741030264819461)
                  ·
                    refine ⟨2807654708951443174653649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14974158447741030264819461 2807654708951443174653649)
                    ·
                      refine ⟨2105741031713582380990237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2807654708951443174653649 2105741031713582380990237)
                      ·
                        rfl

theorem cell23_4100916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 2, 1, 4, 2].length) (baseStart_4100916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4100916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4100916 prefixEnd_4100916 := by exact prefixLift 4100916
  have htrace : WordTrace (prefixWord ++ tailWord_4100916) baseStart_4100916 baseEnd_4100916 := by
    simpa [prefixWord, tailWord_4100916, baseEnd_4100916] using wordTrace_append hprefix tailTrace_4100916
  have hstable : (prefixWord ++ tailWord_4100916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100916).length < 2 ^ (prefixWord ++ tailWord_4100916).sum := by decide
  have hdescent : baseEnd_4100916 < baseStart_4100916 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100972 : List Nat := [2, 2, 1, 1, 4, 1, 1, 2, 1, 6, 2]
def baseStart_4100972 : Nat := 118140960795 + 4100972 * 2 ^ 59
def prefixEnd_4100972 : Nat := 4983230072969 + 3 ^ 40 * 4100972 * 2
def baseEnd_4100972 : Nat := 2105769786630234161889979

theorem tailTrace_4100972 : CollatzResearch.WordTrace tailWord_4100972 prefixEnd_4100972 2105769786630234161889979 := by
  unfold tailWord_4100972
  simp only [CollatzResearch.WordTrace]
  refine ⟨74787368449443154550896585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99716491265924206067862113 74787368449443154550896585)
  ·
    refine ⟨56090526337082365913172439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74787368449443154550896585 56090526337082365913172439)
    ·
      refine ⟨84135789505623548869758659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56090526337082365913172439 84135789505623548869758659)
      ·
        refine ⟨126203684258435323304637989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84135789505623548869758659 126203684258435323304637989)
        ·
          refine ⟨23663190798456623119619623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126203684258435323304637989 23663190798456623119619623)
          ·
            refine ⟨35494786197684934679429435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23663190798456623119619623 35494786197684934679429435)
            ·
              refine ⟨53242179296527402019144153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35494786197684934679429435 53242179296527402019144153)
              ·
                refine ⟨39931634472395551514358115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53242179296527402019144153 39931634472395551514358115)
                ·
                  refine ⟨59897451708593327271537173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39931634472395551514358115 59897451708593327271537173)
                  ·
                    refine ⟨2807693048840312215853305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 59897451708593327271537173 2807693048840312215853305)
                    ·
                      refine ⟨2105769786630234161889979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2807693048840312215853305 2105769786630234161889979)
                      ·
                        rfl

theorem cell23_4100972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 6, 2].length) (baseStart_4100972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4100972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4100972 prefixEnd_4100972 := by exact prefixLift 4100972
  have htrace : WordTrace (prefixWord ++ tailWord_4100972) baseStart_4100972 baseEnd_4100972 := by
    simpa [prefixWord, tailWord_4100972, baseEnd_4100972] using wordTrace_append hprefix tailTrace_4100972
  have hstable : (prefixWord ++ tailWord_4100972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100972).length < 2 ^ (prefixWord ++ tailWord_4100972).sum := by decide
  have hdescent : baseEnd_4100972 < baseStart_4100972 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100985 : List Nat := [1, 2, 1, 3, 2, 3, 1, 1, 2, 1, 6]
def baseStart_4100985 : Nat := 118140960795 + 4100985 * 2 ^ 59
def prefixEnd_4100985 : Nat := 4983230072969 + 3 ^ 40 * 4100985 * 2
def baseEnd_4100985 : Nat := 2105776461878742611027419

theorem tailTrace_4100985 : CollatzResearch.WordTrace tailWord_4100985 prefixEnd_4100985 2105776461878742611027419 := by
  unfold tailWord_4100985
  simp only [CollatzResearch.WordTrace]
  refine ⟨149575211047839212322016409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99716807365226141548010939 149575211047839212322016409)
  ·
    refine ⟨112181408285879409241512307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149575211047839212322016409 112181408285879409241512307)
    ·
      refine ⟨168272112428819113862268461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112181408285879409241512307 168272112428819113862268461)
      ·
        refine ⟨63102042160807167698350673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168272112428819113862268461 63102042160807167698350673)
        ·
          refine ⟨47326531620605375773763005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63102042160807167698350673 47326531620605375773763005)
          ·
            refine ⟨17747449357727015915161127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47326531620605375773763005 17747449357727015915161127)
            ·
              refine ⟨26621174036590523872741691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17747449357727015915161127 26621174036590523872741691)
              ·
                refine ⟨39931761054885785809112537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26621174036590523872741691 39931761054885785809112537)
                ·
                  refine ⟨29948820791164339356834403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39931761054885785809112537 29948820791164339356834403)
                  ·
                    refine ⟨44923231186746509035251605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29948820791164339356834403 44923231186746509035251605)
                    ·
                      refine ⟨2105776461878742611027419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44923231186746509035251605 2105776461878742611027419)
                      ·
                        rfl

theorem cell23_4100985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 1, 6].length) (baseStart_4100985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4100985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4100985 prefixEnd_4100985 := by exact prefixLift 4100985
  have htrace : WordTrace (prefixWord ++ tailWord_4100985) baseStart_4100985 baseEnd_4100985 := by
    simpa [prefixWord, tailWord_4100985, baseEnd_4100985] using wordTrace_append hprefix tailTrace_4100985
  have hstable : (prefixWord ++ tailWord_4100985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100985).length < 2 ^ (prefixWord ++ tailWord_4100985).sum := by decide
  have hdescent : baseEnd_4100985 < baseStart_4100985 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100995 : List Nat := [1, 1, 1, 3, 4, 1, 3, 1, 8]
def baseStart_4100995 : Nat := 118140960795 + 4100995 * 2 ^ 59
def prefixEnd_4100995 : Nat := 4983230072969 + 3 ^ 40 * 4100995 * 2
def baseEnd_4100995 : Nat := 233975732965031952433597

theorem tailTrace_4100995 : CollatzResearch.WordTrace tailWord_4100995 prefixEnd_4100995 233975732965031952433597 := by
  unfold tailWord_4100995
  simp only [CollatzResearch.WordTrace]
  refine ⟨149575575777802984029880439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99717050518535322686586959 149575575777802984029880439)
  ·
    refine ⟨224363363666704476044820659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149575575777802984029880439 224363363666704476044820659)
    ·
      refine ⟨336545045500056714067230989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224363363666704476044820659 336545045500056714067230989)
      ·
        refine ⟨126204392062521267775211621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 336545045500056714067230989 126204392062521267775211621)
        ·
          refine ⟨23663323511722737707852179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126204392062521267775211621 23663323511722737707852179)
          ·
            refine ⟨35494985267584106561778269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23663323511722737707852179 35494985267584106561778269)
            ·
              refine ⟨13310619475344039960666851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35494985267584106561778269 13310619475344039960666851)
              ·
                refine ⟨19965929213016059941000277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13310619475344039960666851 19965929213016059941000277)
                ·
                  refine ⟨233975732965031952433597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19965929213016059941000277 233975732965031952433597)
                  ·
                    rfl

theorem cell23_4100995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 8].length) (baseStart_4100995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4100995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4100995 prefixEnd_4100995 := by exact prefixLift 4100995
  have htrace : WordTrace (prefixWord ++ tailWord_4100995) baseStart_4100995 baseEnd_4100995 := by
    simpa [prefixWord, tailWord_4100995, baseEnd_4100995] using wordTrace_append hprefix tailTrace_4100995
  have hstable : (prefixWord ++ tailWord_4100995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100995).length < 2 ^ (prefixWord ++ tailWord_4100995).sum := by decide
  have hdescent : baseEnd_4100995 < baseStart_4100995 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100999 : List Nat := [1, 1, 4, 2, 3, 2, 2, 1, 3, 4]
def baseStart_4100999 : Nat := 118140960795 + 4100999 * 2 ^ 59
def prefixEnd_4100999 : Nat := 4983230072969 + 3 ^ 40 * 4100999 * 2
def baseEnd_4100999 : Nat := 701927883535968518750785

theorem tailTrace_4100999 : CollatzResearch.WordTrace tailWord_4100999 prefixEnd_4100999 701927883535968518750785 := by
  unfold tailWord_4100999
  simp only [CollatzResearch.WordTrace]
  refine ⟨149575721669788492713026051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99717147779858995142017367 149575721669788492713026051)
  ·
    refine ⟨224363582504682739069539077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149575721669788492713026051 224363582504682739069539077)
    ·
      refine ⟨42068171719628013575538577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 224363582504682739069539077 42068171719628013575538577)
      ·
        refine ⟨31551128789721010181653933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42068171719628013575538577 31551128789721010181653933)
        ·
          refine ⟨11831673296145378818120225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31551128789721010181653933 11831673296145378818120225)
          ·
            refine ⟨8873754972109034113590169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11831673296145378818120225 8873754972109034113590169)
            ·
              refine ⟨6655316229081775585192627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8873754972109034113590169 6655316229081775585192627)
              ·
                refine ⟨9982974343622663377788941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6655316229081775585192627 9982974343622663377788941)
                ·
                  refine ⟨3743615378858498766670853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9982974343622663377788941 3743615378858498766670853)
                  ·
                    refine ⟨701927883535968518750785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3743615378858498766670853 701927883535968518750785)
                    ·
                      rfl

theorem cell23_4100999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 1, 3, 4].length) (baseStart_4100999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4100999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4100999 prefixEnd_4100999 := by exact prefixLift 4100999
  have htrace : WordTrace (prefixWord ++ tailWord_4100999) baseStart_4100999 baseEnd_4100999 := by
    simpa [prefixWord, tailWord_4100999, baseEnd_4100999] using wordTrace_append hprefix tailTrace_4100999
  have hstable : (prefixWord ++ tailWord_4100999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100999).length < 2 ^ (prefixWord ++ tailWord_4100999).sum := by decide
  have hdescent : baseEnd_4100999 < baseStart_4100999 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101015 : List Nat := [1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 6]
def baseStart_4101015 : Nat := 118140960795 + 4101015 * 2 ^ 59
def prefixEnd_4101015 : Nat := 4983230072969 + 3 ^ 40 * 4101015 * 2
def baseEnd_4101015 : Nat := 2105791866298377493652281

theorem tailTrace_4101015 : CollatzResearch.WordTrace tailWord_4101015 prefixEnd_4101015 2105791866298377493652281 := by
  unfold tailWord_4101015
  simp only [CollatzResearch.WordTrace]
  refine ⟨149576305237730527445608499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99717536825153684963738999 149576305237730527445608499)
  ·
    refine ⟨224364457856595791168412749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149576305237730527445608499 224364457856595791168412749)
    ·
      refine ⟨84136671696223421688154781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224364457856595791168412749 84136671696223421688154781)
      ·
        refine ⟨31551251886083783133058043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84136671696223421688154781 31551251886083783133058043)
        ·
          refine ⟨47326877829125674699587065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31551251886083783133058043 47326877829125674699587065)
          ·
            refine ⟨35495158371844256024690299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47326877829125674699587065 35495158371844256024690299)
            ·
              refine ⟨53242737557766384037035449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35495158371844256024690299 53242737557766384037035449)
              ·
                refine ⟨39932053168324788027776587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53242737557766384037035449 39932053168324788027776587)
                ·
                  refine ⟨59898079752487182041664881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39932053168324788027776587 59898079752487182041664881)
                  ·
                    refine ⟨44923559814365386531248661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59898079752487182041664881 44923559814365386531248661)
                    ·
                      refine ⟨2105791866298377493652281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44923559814365386531248661 2105791866298377493652281)
                      ·
                        rfl

theorem cell23_4101015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_4101015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4101015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4101015 prefixEnd_4101015 := by exact prefixLift 4101015
  have htrace : WordTrace (prefixWord ++ tailWord_4101015) baseStart_4101015 baseEnd_4101015 := by
    simpa [prefixWord, tailWord_4101015, baseEnd_4101015] using wordTrace_append hprefix tailTrace_4101015
  have hstable : (prefixWord ++ tailWord_4101015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101015).length < 2 ^ (prefixWord ++ tailWord_4101015).sum := by decide
  have hdescent : baseEnd_4101015 < baseStart_4101015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101049 : List Nat := [1, 2, 1, 4, 2, 2, 1, 1, 4, 3, 2]
def baseStart_4101049 : Nat := 118140960795 + 4101049 * 2 ^ 59
def prefixEnd_4101049 : Nat := 4983230072969 + 3 ^ 40 * 4101049 * 2
def baseEnd_4101049 : Nat := 2105809324640630360627125

theorem tailTrace_4101049 : CollatzResearch.WordTrace tailWord_4101049 prefixEnd_4101049 2105809324640630360627125 := by
  unfold tailWord_4101049
  simp only [CollatzResearch.WordTrace]
  refine ⟨149577545319607351252346201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99718363546404900834897467 149577545319607351252346201)
  ·
    refine ⟨112183158989705513439259651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149577545319607351252346201 112183158989705513439259651)
    ·
      refine ⟨168274738484558270158889477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112183158989705513439259651 168274738484558270158889477)
      ·
        refine ⟨31551513465854675654791777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168274738484558270158889477 31551513465854675654791777)
        ·
          refine ⟨23663635099391006741093833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31551513465854675654791777 23663635099391006741093833)
          ·
            refine ⟨17747726324543255055820375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23663635099391006741093833 17747726324543255055820375)
            ·
              refine ⟨26621589486814882583730563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17747726324543255055820375 26621589486814882583730563)
              ·
                refine ⟨39932384230222323875595845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26621589486814882583730563 39932384230222323875595845)
                ·
                  refine ⟨7487322043166685726674221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39932384230222323875595845 7487322043166685726674221)
                  ·
                    refine ⟨2807745766187507147502833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7487322043166685726674221 2807745766187507147502833)
                    ·
                      refine ⟨2105809324640630360627125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2807745766187507147502833 2105809324640630360627125)
                      ·
                        rfl

theorem cell23_4101049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 4, 3, 2].length) (baseStart_4101049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4101049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4101049 prefixEnd_4101049 := by exact prefixLift 4101049
  have htrace : WordTrace (prefixWord ++ tailWord_4101049) baseStart_4101049 baseEnd_4101049 := by
    simpa [prefixWord, tailWord_4101049, baseEnd_4101049] using wordTrace_append hprefix tailTrace_4101049
  have hstable : (prefixWord ++ tailWord_4101049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101049).length < 2 ^ (prefixWord ++ tailWord_4101049).sum := by decide
  have hdescent : baseEnd_4101049 < baseStart_4101049 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101055 : List Nat := [1, 1, 2, 2, 2, 1, 2, 1, 5, 6]
def baseStart_4101055 : Nat := 118140960795 + 4101055 * 2 ^ 59
def prefixEnd_4101055 : Nat := 4983230072969 + 3 ^ 40 * 4101055 * 2
def baseEnd_4101055 : Nat := 701937468508185779050699

theorem tailTrace_4101055 : CollatzResearch.WordTrace tailWord_4101055 prefixEnd_4101055 701937468508185779050699 := by
  unfold tailWord_4101055
  simp only [CollatzResearch.WordTrace]
  refine ⟨149577764157585614277064619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99718509438390409518043079 149577764157585614277064619)
  ·
    refine ⟨224366646236378421415596929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149577764157585614277064619 224366646236378421415596929)
    ·
      refine ⟨168274984677283816061697697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224366646236378421415596929 168274984677283816061697697)
      ·
        refine ⟨126206238507962862046273273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168274984677283816061697697 126206238507962862046273273)
        ·
          refine ⟨94654678880972146534704955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126206238507962862046273273 94654678880972146534704955)
          ·
            refine ⟨141982018321458219802057433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94654678880972146534704955 141982018321458219802057433)
            ·
              refine ⟨106486513741093664851543075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141982018321458219802057433 106486513741093664851543075)
              ·
                refine ⟨159729770611640497277314613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106486513741093664851543075 159729770611640497277314613)
                ·
                  refine ⟨14974665994841296619748245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 159729770611640497277314613 14974665994841296619748245)
                  ·
                    refine ⟨701937468508185779050699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14974665994841296619748245 701937468508185779050699)
                    ·
                      rfl

theorem cell23_4101055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 5, 6].length) (baseStart_4101055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4101055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4101055 prefixEnd_4101055 := by exact prefixLift 4101055
  have htrace : WordTrace (prefixWord ++ tailWord_4101055) baseStart_4101055 baseEnd_4101055 := by
    simpa [prefixWord, tailWord_4101055, baseEnd_4101055] using wordTrace_append hprefix tailTrace_4101055
  have hstable : (prefixWord ++ tailWord_4101055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101055).length < 2 ^ (prefixWord ++ tailWord_4101055).sum := by decide
  have hdescent : baseEnd_4101055 < baseStart_4101055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101056 : List Nat := [2, 1, 1, 2, 3, 5, 1, 1, 3, 1, 3]
def baseStart_4101056 : Nat := 118140960795 + 4101056 * 2 ^ 59
def prefixEnd_4101056 : Nat := 4983230072969 + 3 ^ 40 * 4101056 * 2
def baseEnd_4101056 : Nat := 2105812919005211833239593

theorem tailTrace_4101056 : CollatzResearch.WordTrace tailWord_4101056 prefixEnd_4101056 2105812919005211833239593 := by
  unfold tailWord_4101056
  simp only [CollatzResearch.WordTrace]
  refine ⟨74788900315290995723925511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99718533753721327631900681 74788900315290995723925511)
  ·
    refine ⟨112183350472936493585888267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74788900315290995723925511 112183350472936493585888267)
    ·
      refine ⟨168275025709404740378832401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112183350472936493585888267 168275025709404740378832401)
      ·
        refine ⟨126206269282053555284124301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168275025709404740378832401 126206269282053555284124301)
        ·
          refine ⟨47327350980770083231546613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126206269282053555284124301 47327350980770083231546613)
          ·
            refine ⟨4436939154447195302957495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47327350980770083231546613 4436939154447195302957495)
            ·
              refine ⟨6655408731670792954436243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4436939154447195302957495 6655408731670792954436243)
              ·
                refine ⟨9983113097506189431654365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6655408731670792954436243 9983113097506189431654365)
                ·
                  refine ⟨3743667411564821036870387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9983113097506189431654365 3743667411564821036870387)
                  ·
                    refine ⟨5615501117347231555305581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3743667411564821036870387 5615501117347231555305581)
                    ·
                      refine ⟨2105812919005211833239593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5615501117347231555305581 2105812919005211833239593)
                      ·
                        rfl

theorem cell23_4101056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 1, 3, 1, 3].length) (baseStart_4101056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4101056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4101056 prefixEnd_4101056 := by exact prefixLift 4101056
  have htrace : WordTrace (prefixWord ++ tailWord_4101056) baseStart_4101056 baseEnd_4101056 := by
    simpa [prefixWord, tailWord_4101056, baseEnd_4101056] using wordTrace_append hprefix tailTrace_4101056
  have hstable : (prefixWord ++ tailWord_4101056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101056).length < 2 ^ (prefixWord ++ tailWord_4101056).sum := by decide
  have hdescent : baseEnd_4101056 < baseStart_4101056 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101076 : List Nat := [2, 4, 1, 2, 1, 4, 1, 2, 1, 5]
def baseStart_4101076 : Nat := 118140960795 + 4101076 * 2 ^ 59
def prefixEnd_4101076 : Nat := 4983230072969 + 3 ^ 40 * 4101076 * 2
def baseEnd_4101076 : Nat := 701941062872767251663167

theorem tailTrace_4101076 : CollatzResearch.WordTrace tailWord_4101076 prefixEnd_4101076 701941062872767251663167 := by
  unfold tailWord_4101076
  simp only [CollatzResearch.WordTrace]
  refine ⟨74789265045254767431789541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99719020060339689909052721 74789265045254767431789541)
  ·
    refine ⟨14022987195985268893460539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74789265045254767431789541 14022987195985268893460539)
    ·
      refine ⟨21034480793977903340190809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14022987195985268893460539 21034480793977903340190809)
      ·
        refine ⟨15775860595483427505143107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21034480793977903340190809 15775860595483427505143107)
        ·
          refine ⟨23663790893225141257714661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15775860595483427505143107 23663790893225141257714661)
          ·
            refine ⟨4436960792479713985821499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23663790893225141257714661 4436960792479713985821499)
            ·
              refine ⟨6655441188719570978732249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4436960792479713985821499 6655441188719570978732249)
              ·
                refine ⟨4991580891539678234049187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6655441188719570978732249 4991580891539678234049187)
                ·
                  refine ⟨7487371337309517351073781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4991580891539678234049187 7487371337309517351073781)
                  ·
                    refine ⟨701941062872767251663167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7487371337309517351073781 701941062872767251663167)
                    ·
                      rfl

theorem cell23_4101076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 2, 1, 5].length) (baseStart_4101076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4101076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4101076 prefixEnd_4101076 := by exact prefixLift 4101076
  have htrace : WordTrace (prefixWord ++ tailWord_4101076) baseStart_4101076 baseEnd_4101076 := by
    simpa [prefixWord, tailWord_4101076, baseEnd_4101076] using wordTrace_append hprefix tailTrace_4101076
  have hstable : (prefixWord ++ tailWord_4101076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101076).length < 2 ^ (prefixWord ++ tailWord_4101076).sum := by decide
  have hdescent : baseEnd_4101076 < baseStart_4101076 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101093 : List Nat := [1, 3, 1, 6, 1, 1, 3, 1, 1, 5]
def baseStart_4101093 : Nat := 118140960795 + 4101093 * 2 ^ 59
def prefixEnd_4101093 : Nat := 4983230072969 + 3 ^ 40 * 4101093 * 2
def baseEnd_4101093 : Nat := 701943972596476062825641

theorem tailTrace_4101093 : CollatzResearch.WordTrace tailWord_4101093 prefixEnd_4101093 701943972596476062825641 := by
  unfold tailWord_4101093
  simp only [CollatzResearch.WordTrace]
  refine ⟨149579150131447946766947933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99719433420965297844631955 149579150131447946766947933)
  ·
    refine ⟨56092181299292980037605475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149579150131447946766947933 56092181299292980037605475)
    ·
      refine ⟨84138271948939470056408213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56092181299292980037605475 84138271948939470056408213)
      ·
        refine ⟨3943981497606537658894135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 84138271948939470056408213 3943981497606537658894135)
        ·
          refine ⟨5915972246409806488341203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3943981497606537658894135 5915972246409806488341203)
          ·
            refine ⟨8873958369614709732511805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5915972246409806488341203 8873958369614709732511805)
            ·
              refine ⟨3327734388605516149691927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8873958369614709732511805 3327734388605516149691927)
              ·
                refine ⟨4991601582908274224537891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3327734388605516149691927 4991601582908274224537891)
                ·
                  refine ⟨7487402374362411336806837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4991601582908274224537891 7487402374362411336806837)
                  ·
                    refine ⟨701943972596476062825641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7487402374362411336806837 701943972596476062825641)
                    ·
                      rfl

theorem cell23_4101093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 3, 1, 1, 5].length) (baseStart_4101093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4101093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4101093 prefixEnd_4101093 := by exact prefixLift 4101093
  have htrace : WordTrace (prefixWord ++ tailWord_4101093) baseStart_4101093 baseEnd_4101093 := by
    simpa [prefixWord, tailWord_4101093, baseEnd_4101093] using wordTrace_append hprefix tailTrace_4101093
  have hstable : (prefixWord ++ tailWord_4101093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101093).length < 2 ^ (prefixWord ++ tailWord_4101093).sum := by decide
  have hdescent : baseEnd_4101093 < baseStart_4101093 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101102 : List Nat := [4, 1, 2, 1, 4, 11]
def baseStart_4101102 : Nat := 118140960795 + 4101102 * 2 ^ 59
def prefixEnd_4101102 : Nat := 4983230072969 + 3 ^ 40 * 4101102 * 2
def baseEnd_4101102 : Nat := 8665993988128883346767

theorem tailTrace_4101102 : CollatzResearch.WordTrace tailWord_4101102 prefixEnd_4101102 8665993988128883346767 := by
  unfold tailWord_4101102
  simp only [CollatzResearch.WordTrace]
  refine ⟨18697434798551917663003195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99719652258943560869350373 18697434798551917663003195)
  ·
    refine ⟨28046152197827876494504793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18697434798551917663003195 28046152197827876494504793)
    ·
      refine ⟨21034614148370907370878595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28046152197827876494504793 21034614148370907370878595)
      ·
        refine ⟨31551921222556361056317893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21034614148370907370878595 31551921222556361056317893)
        ·
          refine ⟨5915985229229317698059605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31551921222556361056317893 5915985229229317698059605)
          ·
            refine ⟨8665993988128883346767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 5915985229229317698059605 8665993988128883346767)
            ·
              rfl

theorem cell23_4101102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 11].length) (baseStart_4101102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4101102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4101102 prefixEnd_4101102 := by exact prefixLift 4101102
  have htrace : WordTrace (prefixWord ++ tailWord_4101102) baseStart_4101102 baseEnd_4101102 := by
    simpa [prefixWord, tailWord_4101102, baseEnd_4101102] using wordTrace_append hprefix tailTrace_4101102
  have hstable : (prefixWord ++ tailWord_4101102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101102).length < 2 ^ (prefixWord ++ tailWord_4101102).sum := by decide
  have hdescent : baseEnd_4101102 < baseStart_4101102 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101112 : List Nat := [2, 1, 2, 1, 1, 3, 1, 1, 5, 3, 3]
def baseStart_4101112 : Nat := 118140960795 + 4101112 * 2 ^ 59
def prefixEnd_4101112 : Nat := 4983230072969 + 3 ^ 40 * 4101112 * 2
def baseEnd_4101112 : Nat := 2105841673921863614139335

theorem tailTrace_4101112 : CollatzResearch.WordTrace tailWord_4101112 prefixEnd_4101112 2105841673921863614139335 := by
  unfold tailWord_4101112
  simp only [CollatzResearch.WordTrace]
  refine ⟨74789921559189556505944795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99719895412252742007926393 74789921559189556505944795)
  ·
    refine ⟨112184882338784334758917193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74789921559189556505944795 112184882338784334758917193)
    ·
      refine ⟨84138661754088251069187895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112184882338784334758917193 84138661754088251069187895)
      ·
        refine ⟨126207992631132376603781843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84138661754088251069187895 126207992631132376603781843)
        ·
          refine ⟨189311988946698564905672765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126207992631132376603781843 189311988946698564905672765)
          ·
            refine ⟨70991995855011961839627287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189311988946698564905672765 70991995855011961839627287)
            ·
              refine ⟨106487993782517942759440931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70991995855011961839627287 106487993782517942759440931)
              ·
                refine ⟨159731990673776914139161397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106487993782517942759440931 159731990673776914139161397)
                ·
                  refine ⟨14974874125666585700546381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 159731990673776914139161397 14974874125666585700546381)
                  ·
                    refine ⟨5615577797124969637704893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14974874125666585700546381 5615577797124969637704893)
                    ·
                      refine ⟨2105841673921863614139335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5615577797124969637704893 2105841673921863614139335)
                      ·
                        rfl

theorem cell23_4101112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 5, 3, 3].length) (baseStart_4101112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4101112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4101112 prefixEnd_4101112 := by exact prefixLift 4101112
  have htrace : WordTrace (prefixWord ++ tailWord_4101112) baseStart_4101112 baseEnd_4101112 := by
    simpa [prefixWord, tailWord_4101112, baseEnd_4101112] using wordTrace_append hprefix tailTrace_4101112
  have hstable : (prefixWord ++ tailWord_4101112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101112).length < 2 ^ (prefixWord ++ tailWord_4101112).sum := by decide
  have hdescent : baseEnd_4101112 < baseStart_4101112 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101113 : List Nat := [1, 2, 1, 3, 1, 3, 3, 4, 1, 2, 2]
def baseStart_4101113 : Nat := 118140960795 + 4101113 * 2 ^ 59
def prefixEnd_4101113 : Nat := 4983230072969 + 3 ^ 40 * 4101113 * 2
def baseEnd_4101113 : Nat := 2105842187402518110226831

theorem tailTrace_4101113 : CollatzResearch.WordTrace tailWord_4101113 prefixEnd_4101113 2105842187402518110226831 := by
  unfold tailWord_4101113
  simp only [CollatzResearch.WordTrace]
  refine ⟨149579879591375490182675993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99719919727583660121783995 149579879591375490182675993)
  ·
    refine ⟨112184909693531617637006995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149579879591375490182675993 112184909693531617637006995)
    ·
      refine ⟨168277364540297426455510493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112184909693531617637006995 168277364540297426455510493)
      ·
        refine ⟨63104011702611534920816435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168277364540297426455510493 63104011702611534920816435)
        ·
          refine ⟨94656017553917302381224653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63104011702611534920816435 94656017553917302381224653)
          ·
            refine ⟨35496006582718988392959245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94656017553917302381224653 35496006582718988392959245)
            ·
              refine ⟨13311002468519620647359717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35496006582718988392959245 13311002468519620647359717)
              ·
                refine ⟨2495812962847428871379947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13311002468519620647359717 2495812962847428871379947)
                ·
                  refine ⟨3743719444271143307069921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2495812962847428871379947 3743719444271143307069921)
                  ·
                    refine ⟨2807789583203357480302441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3743719444271143307069921 2807789583203357480302441)
                    ·
                      refine ⟨2105842187402518110226831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2807789583203357480302441 2105842187402518110226831)
                      ·
                        rfl

theorem cell23_4101113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 4, 1, 2, 2].length) (baseStart_4101113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4101113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4101113 prefixEnd_4101113 := by exact prefixLift 4101113
  have htrace : WordTrace (prefixWord ++ tailWord_4101113) baseStart_4101113 baseEnd_4101113 := by
    simpa [prefixWord, tailWord_4101113, baseEnd_4101113] using wordTrace_append hprefix tailTrace_4101113
  have hstable : (prefixWord ++ tailWord_4101113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101113).length < 2 ^ (prefixWord ++ tailWord_4101113).sum := by decide
  have hdescent : baseEnd_4101113 < baseStart_4101113 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101190 : List Nat := [6, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2]
def baseStart_4101190 : Nat := 118140960795 + 4101190 * 2 ^ 59
def prefixEnd_4101190 : Nat := 4983230072969 + 3 ^ 40 * 4101190 * 2
def baseEnd_4101190 : Nat := 2105881725412914308963977

theorem tailTrace_4101190 : CollatzResearch.WordTrace tailWord_4101190 prefixEnd_4101190 2105881725412914308963977 := by
  unfold tailWord_4101190
  simp only [CollatzResearch.WordTrace]
  refine ⟨4674459000378016635413407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 99721792008064354888819349 4674459000378016635413407)
  ·
    refine ⟨7011688500567024953120111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4674459000378016635413407 7011688500567024953120111)
    ·
      refine ⟨10517532750850537429680167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7011688500567024953120111 10517532750850537429680167)
      ·
        refine ⟨15776299126275806144520251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10517532750850537429680167 15776299126275806144520251)
        ·
          refine ⟨23664448689413709216780377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15776299126275806144520251 23664448689413709216780377)
          ·
            refine ⟨17748336517060281912585283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23664448689413709216780377 17748336517060281912585283)
            ·
              refine ⟨26622504775590422868877925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17748336517060281912585283 26622504775590422868877925)
              ·
                refine ⟨4991719645423204287914611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26622504775590422868877925 4991719645423204287914611)
                ·
                  refine ⟨7487579468134806431871917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4991719645423204287914611 7487579468134806431871917)
                  ·
                    refine ⟨2807842300550552411951969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7487579468134806431871917 2807842300550552411951969)
                    ·
                      refine ⟨2105881725412914308963977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2807842300550552411951969 2105881725412914308963977)
                      ·
                        rfl

theorem cell23_4101190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2].length) (baseStart_4101190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4101190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4101190 prefixEnd_4101190 := by exact prefixLift 4101190
  have htrace : WordTrace (prefixWord ++ tailWord_4101190) baseStart_4101190 baseEnd_4101190 := by
    simpa [prefixWord, tailWord_4101190, baseEnd_4101190] using wordTrace_append hprefix tailTrace_4101190
  have hstable : (prefixWord ++ tailWord_4101190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101190).length < 2 ^ (prefixWord ++ tailWord_4101190).sum := by decide
  have hdescent : baseEnd_4101190 < baseStart_4101190 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101192 : List Nat := [2, 1, 3, 1, 1, 1, 3, 4, 7]
def baseStart_4101192 : Nat := 118140960795 + 4101192 * 2 ^ 59
def prefixEnd_4101192 : Nat := 4983230072969 + 3 ^ 40 * 4101192 * 2
def baseEnd_4101192 : Nat := 233986972486024811237663

theorem tailTrace_4101192 : CollatzResearch.WordTrace tailWord_4101192 prefixEnd_4101192 233986972486024811237663 := by
  unfold tailWord_4101192
  simp only [CollatzResearch.WordTrace]
  refine ⟨74791380479044643337400915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99721840638726191116534553 74791380479044643337400915)
  ·
    refine ⟨112187070718566965006101373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74791380479044643337400915 112187070718566965006101373)
    ·
      refine ⟨42070151519462611877288015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112187070718566965006101373 42070151519462611877288015)
      ·
        refine ⟨63105227279193917815932023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42070151519462611877288015 63105227279193917815932023)
        ·
          refine ⟨94657840918790876723898035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63105227279193917815932023 94657840918790876723898035)
          ·
            refine ⟨141986761378186315085847053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94657840918790876723898035 141986761378186315085847053)
            ·
              refine ⟨53245035516819868157192645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141986761378186315085847053 53245035516819868157192645)
              ·
                refine ⟨9983444159403725279473621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53245035516819868157192645 9983444159403725279473621)
                ·
                  refine ⟨233986972486024811237663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9983444159403725279473621 233986972486024811237663)
                  ·
                    rfl

theorem cell23_4101192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 4, 7].length) (baseStart_4101192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4101192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4101192 prefixEnd_4101192 := by exact prefixLift 4101192
  have htrace : WordTrace (prefixWord ++ tailWord_4101192) baseStart_4101192 baseEnd_4101192 := by
    simpa [prefixWord, tailWord_4101192, baseEnd_4101192] using wordTrace_append hprefix tailTrace_4101192
  have hstable : (prefixWord ++ tailWord_4101192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101192).length < 2 ^ (prefixWord ++ tailWord_4101192).sum := by decide
  have hdescent : baseEnd_4101192 < baseStart_4101192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101209 : List Nat := [1, 2, 1, 2, 2, 1, 2, 7, 5]
def baseStart_4101209 : Nat := 118140960795 + 4101209 * 2 ^ 59
def prefixEnd_4101209 : Nat := 4983230072969 + 3 ^ 40 * 4101209 * 2
def baseEnd_4101209 : Nat := 233987942393927748291821

theorem tailTrace_4101209 : CollatzResearch.WordTrace tailWord_4101209 prefixEnd_4101209 233987942393927748291821 := by
  unfold tailWord_4101209
  simp only [CollatzResearch.WordTrace]
  refine ⟨149583380999027698578170681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99722253999351799052113787 149583380999027698578170681)
  ·
    refine ⟨112187535749270773933628011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149583380999027698578170681 112187535749270773933628011)
    ·
      refine ⟨168281303623906160900442017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112187535749270773933628011 168281303623906160900442017)
      ·
        refine ⟨126210977717929620675331513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168281303623906160900442017 126210977717929620675331513)
        ·
          refine ⟨94658233288447215506498635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126210977717929620675331513 94658233288447215506498635)
          ·
            refine ⟨141987349932670823259747953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94658233288447215506498635 141987349932670823259747953)
            ·
              refine ⟨106490512449503117444810965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141987349932670823259747953 106490512449503117444810965)
              ·
                refine ⟨2495871385535229315112757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 106490512449503117444810965 2495871385535229315112757)
                ·
                  refine ⟨233987942393927748291821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2495871385535229315112757 233987942393927748291821)
                  ·
                    rfl

theorem cell23_4101209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 7, 5].length) (baseStart_4101209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4101209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4101209 prefixEnd_4101209 := by exact prefixLift 4101209
  have htrace : WordTrace (prefixWord ++ tailWord_4101209) baseStart_4101209 baseEnd_4101209 := by
    simpa [prefixWord, tailWord_4101209, baseEnd_4101209] using wordTrace_append hprefix tailTrace_4101209
  have hstable : (prefixWord ++ tailWord_4101209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101209).length < 2 ^ (prefixWord ++ tailWord_4101209).sum := by decide
  have hdescent : baseEnd_4101209 < baseStart_4101209 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101226 : List Nat := [3, 1, 3, 2, 2, 3, 1, 1, 7]
def baseStart_4101226 : Nat := 118140960795 + 4101226 * 2 ^ 59
def prefixEnd_4101226 : Nat := 4983230072969 + 3 ^ 40 * 4101226 * 2
def baseEnd_4101226 : Nat := 233988912301830685345979

theorem tailTrace_4101226 : CollatzResearch.WordTrace tailWord_4101226 prefixEnd_4101226 233988912301830685345979 := by
  unfold tailWord_4101226
  simp only [CollatzResearch.WordTrace]
  refine ⟨37396000259991527620384883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99722667359977406987693021 37396000259991527620384883)
  ·
    refine ⟨56094000389987291430577325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37396000259991527620384883 56094000389987291430577325)
    ·
      refine ⟨21035250146245234286466497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56094000389987291430577325 21035250146245234286466497)
      ·
        refine ⟨15776437609683925714849873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21035250146245234286466497 15776437609683925714849873)
        ·
          refine ⟨11832328207262944286137405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15776437609683925714849873 11832328207262944286137405)
          ·
            refine ⟨4437123077723604107301527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11832328207262944286137405 4437123077723604107301527)
            ·
              refine ⟨6655684616585406160952291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4437123077723604107301527 6655684616585406160952291)
              ·
                refine ⟨9983526924878109241428437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6655684616585406160952291 9983526924878109241428437)
                ·
                  refine ⟨233988912301830685345979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9983526924878109241428437 233988912301830685345979)
                  ·
                    rfl

theorem cell23_4101226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 1, 7].length) (baseStart_4101226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4101226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4101226 prefixEnd_4101226 := by exact prefixLift 4101226
  have htrace : WordTrace (prefixWord ++ tailWord_4101226) baseStart_4101226 baseEnd_4101226 := by
    simpa [prefixWord, tailWord_4101226, baseEnd_4101226] using wordTrace_append hprefix tailTrace_4101226
  have hstable : (prefixWord ++ tailWord_4101226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101226).length < 2 ^ (prefixWord ++ tailWord_4101226).sum := by decide
  have hdescent : baseEnd_4101226 < baseStart_4101226 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101237 : List Nat := [1, 3, 4, 3, 1, 1, 1, 3, 2, 2, 2]
def baseStart_4101237 : Nat := 118140960795 + 4101237 * 2 ^ 59
def prefixEnd_4101237 : Nat := 4983230072969 + 3 ^ 40 * 4101237 * 2
def baseEnd_4101237 : Nat := 2105905859003675625076261

theorem tailTrace_4101237 : CollatzResearch.WordTrace tailWord_4101237 prefixEnd_4101237 2105905859003675625076261 := by
  unfold tailWord_4101237
  simp only [CollatzResearch.WordTrace]
  refine ⟨149584402242926259360189965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99722934828617506240126643 149584402242926259360189965)
  ·
    refine ⟨56094150841097347260071237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149584402242926259360189965 56094150841097347260071237)
    ·
      refine ⟨10517653282705752611263357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56094150841097347260071237 10517653282705752611263357)
      ·
        refine ⟨3944119981014657229223759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10517653282705752611263357 3944119981014657229223759)
        ·
          refine ⟨5916179971521985843835639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3944119981014657229223759 5916179971521985843835639)
          ·
            refine ⟨8874269957282978765753459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5916179971521985843835639 8874269957282978765753459)
            ·
              refine ⟨13311404935924468148630189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8874269957282978765753459 13311404935924468148630189)
              ·
                refine ⟨4991776850971675555736321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13311404935924468148630189 4991776850971675555736321)
                ·
                  refine ⟨3743832638228756666802241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4991776850971675555736321 3743832638228756666802241)
                  ·
                    refine ⟨2807874478671567500101681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3743832638228756666802241 2807874478671567500101681)
                    ·
                      refine ⟨2105905859003675625076261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2807874478671567500101681 2105905859003675625076261)
                      ·
                        rfl

theorem cell23_4101237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_4101237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4101237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4101237 prefixEnd_4101237 := by exact prefixLift 4101237
  have htrace : WordTrace (prefixWord ++ tailWord_4101237) baseStart_4101237 baseEnd_4101237 := by
    simpa [prefixWord, tailWord_4101237, baseEnd_4101237] using wordTrace_append hprefix tailTrace_4101237
  have hstable : (prefixWord ++ tailWord_4101237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101237).length < 2 ^ (prefixWord ++ tailWord_4101237).sum := by decide
  have hdescent : baseEnd_4101237 < baseStart_4101237 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101269 : List Nat := [1, 3, 2, 1, 1, 1, 2, 1, 7, 4]
def baseStart_4101269 : Nat := 118140960795 + 4101269 * 2 ^ 59
def prefixEnd_4101269 : Nat := 4983230072969 + 3 ^ 40 * 4101269 * 2
def baseEnd_4101269 : Nat := 701974096794873166625371

theorem tailTrace_4101269 : CollatzResearch.WordTrace tailWord_4101269 prefixEnd_4101269 701974096794873166625371 := by
  unfold tailWord_4101269
  simp only [CollatzResearch.WordTrace]
  refine ⟨149585569378810328825354861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99723712919206885883569907 149585569378810328825354861)
  ·
    refine ⟨56094588517053873309508073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149585569378810328825354861 56094588517053873309508073)
    ·
      refine ⟨42070941387790404982131055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56094588517053873309508073 42070941387790404982131055)
      ·
        refine ⟨63106412081685607473196583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42070941387790404982131055 63106412081685607473196583)
        ·
          refine ⟨94659618122528411209794875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63106412081685607473196583 94659618122528411209794875)
          ·
            refine ⟨141989427183792616814692313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94659618122528411209794875 141989427183792616814692313)
            ·
              refine ⟨106492070387844462611019235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141989427183792616814692313 106492070387844462611019235)
              ·
                refine ⟨159738105581766693916528853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106492070387844462611019235 159738105581766693916528853)
                ·
                  refine ⟨3743861849572656888668645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 159738105581766693916528853 3743861849572656888668645)
                  ·
                    refine ⟨701974096794873166625371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3743861849572656888668645 701974096794873166625371)
                    ·
                      rfl

theorem cell23_4101269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 7, 4].length) (baseStart_4101269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4101269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4101269 prefixEnd_4101269 := by exact prefixLift 4101269
  have htrace : WordTrace (prefixWord ++ tailWord_4101269) baseStart_4101269 baseEnd_4101269 := by
    simpa [prefixWord, tailWord_4101269, baseEnd_4101269] using wordTrace_append hprefix tailTrace_4101269
  have hstable : (prefixWord ++ tailWord_4101269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101269).length < 2 ^ (prefixWord ++ tailWord_4101269).sum := by decide
  have hdescent : baseEnd_4101269 < baseStart_4101269 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101276 : List Nat := [2, 2, 3, 2, 1, 2, 2, 2, 2, 1, 4]
def baseStart_4101276 : Nat := 118140960795 + 4101276 * 2 ^ 59
def prefixEnd_4101276 : Nat := 4983230072969 + 3 ^ 40 * 4101276 * 2
def baseEnd_4101276 : Nat := 2105925884749200972488581

theorem tailTrace_4101276 : CollatzResearch.WordTrace tailWord_4101276 prefixEnd_4101276 2105925884749200972488581 := by
  unfold tailWord_4101276
  simp only [CollatzResearch.WordTrace]
  refine ⟨74792912344892484510429841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99723883126523312680573121 74792912344892484510429841)
  ·
    refine ⟨56094684258669363382822381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74792912344892484510429841 56094684258669363382822381)
    ·
      refine ⟨21035506597001011268558393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56094684258669363382822381 21035506597001011268558393)
      ·
        refine ⟨15776629947750758451418795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21035506597001011268558393 15776629947750758451418795)
        ·
          refine ⟨23664944921626137677128193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15776629947750758451418795 23664944921626137677128193)
          ·
            refine ⟨17748708691219603257846145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23664944921626137677128193 17748708691219603257846145)
            ·
              refine ⟨13311531518414702443384609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17748708691219603257846145 13311531518414702443384609)
              ·
                refine ⟨9983648638811026832538457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13311531518414702443384609 9983648638811026832538457)
                ·
                  refine ⟨7487736479108270124403843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9983648638811026832538457 7487736479108270124403843)
                  ·
                    refine ⟨11231604718662405186605765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7487736479108270124403843 11231604718662405186605765)
                    ·
                      refine ⟨2105925884749200972488581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11231604718662405186605765 2105925884749200972488581)
                      ·
                        rfl

theorem cell23_4101276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_4101276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4101276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4101276 prefixEnd_4101276 := by exact prefixLift 4101276
  have htrace : WordTrace (prefixWord ++ tailWord_4101276) baseStart_4101276 baseEnd_4101276 := by
    simpa [prefixWord, tailWord_4101276, baseEnd_4101276] using wordTrace_append hprefix tailTrace_4101276
  have hstable : (prefixWord ++ tailWord_4101276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101276).length < 2 ^ (prefixWord ++ tailWord_4101276).sum := by decide
  have hdescent : baseEnd_4101276 < baseStart_4101276 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101299 : List Nat := [1, 1, 1, 2, 3, 2, 4, 3, 6]
def baseStart_4101299 : Nat := 118140960795 + 4101299 * 2 ^ 59
def prefixEnd_4101299 : Nat := 4983230072969 + 3 ^ 40 * 4101299 * 2
def baseEnd_4101299 : Nat := 233993077200472709166775

theorem tailTrace_4101299 : CollatzResearch.WordTrace tailWord_4101299 prefixEnd_4101299 233993077200472709166775 := by
  unfold tailWord_4101299
  simp only [CollatzResearch.WordTrace]
  refine ⟨149586663568701643948946951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99724442379134429299297967 149586663568701643948946951)
  ·
    refine ⟨224379995353052465923420427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149586663568701643948946951 224379995353052465923420427)
    ·
      refine ⟨336569993029578698885130641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224379995353052465923420427 336569993029578698885130641)
      ·
        refine ⟨252427494772184024163847981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336569993029578698885130641 252427494772184024163847981)
        ·
          refine ⟨94660310539569009061442993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252427494772184024163847981 94660310539569009061442993)
          ·
            refine ⟨70995232904676756796082245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94660310539569009061442993 70995232904676756796082245)
            ·
              refine ⟨13311606169626891899265421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70995232904676756796082245 13311606169626891899265421)
              ·
                refine ⟨4991852313610084462224533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13311606169626891899265421 4991852313610084462224533)
                ·
                  refine ⟨233993077200472709166775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4991852313610084462224533 233993077200472709166775)
                  ·
                    rfl

theorem cell23_4101299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 3, 6].length) (baseStart_4101299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4101299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4101299 prefixEnd_4101299 := by exact prefixLift 4101299
  have htrace : WordTrace (prefixWord ++ tailWord_4101299) baseStart_4101299 baseEnd_4101299 := by
    simpa [prefixWord, tailWord_4101299, baseEnd_4101299] using wordTrace_append hprefix tailTrace_4101299
  have hstable : (prefixWord ++ tailWord_4101299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101299).length < 2 ^ (prefixWord ++ tailWord_4101299).sum := by decide
  have hdescent : baseEnd_4101299 < baseStart_4101299 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101313 : List Nat := [1, 2, 6, 1, 1, 2, 1, 1, 1, 4, 3]
def baseStart_4101313 : Nat := 118140960795 + 4101313 * 2 ^ 59
def prefixEnd_4101313 : Nat := 4983230072969 + 3 ^ 40 * 4101313 * 2
def baseEnd_4101313 : Nat := 2105944883533417327725911

theorem tailTrace_4101313 : CollatzResearch.WordTrace tailWord_4101313 prefixEnd_4101313 2105944883533417327725911 := by
  unfold tailWord_4101313
  simp only [CollatzResearch.WordTrace]
  refine ⟨149587174190650924339956593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99724782793767282893304395 149587174190650924339956593)
  ·
    refine ⟨112190380642988193254967445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149587174190650924339956593 112190380642988193254967445)
    ·
      refine ⟨5258924092640071558826599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 112190380642988193254967445 5258924092640071558826599)
      ·
        refine ⟨7888386138960107338239899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5258924092640071558826599 7888386138960107338239899)
        ·
          refine ⟨11832579208440161007359849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7888386138960107338239899 11832579208440161007359849)
          ·
            refine ⟨8874434406330120755519887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11832579208440161007359849 8874434406330120755519887)
            ·
              refine ⟨13311651609495181133279831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8874434406330120755519887 13311651609495181133279831)
              ·
                refine ⟨19967477414242771699919747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13311651609495181133279831 19967477414242771699919747)
                ·
                  refine ⟨29951216121364157549879621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19967477414242771699919747 29951216121364157549879621)
                  ·
                    refine ⟨5615853022755779540602429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29951216121364157549879621 5615853022755779540602429)
                    ·
                      refine ⟨2105944883533417327725911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5615853022755779540602429 2105944883533417327725911)
                      ·
                        rfl

theorem cell23_4101313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_4101313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4101313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4101313 prefixEnd_4101313 := by exact prefixLift 4101313
  have htrace : WordTrace (prefixWord ++ tailWord_4101313) baseStart_4101313 baseEnd_4101313 := by
    simpa [prefixWord, tailWord_4101313, baseEnd_4101313] using wordTrace_append hprefix tailTrace_4101313
  have hstable : (prefixWord ++ tailWord_4101313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101313).length < 2 ^ (prefixWord ++ tailWord_4101313).sum := by decide
  have hdescent : baseEnd_4101313 < baseStart_4101313 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101333 : List Nat := [1, 3, 2, 4, 1, 3, 1, 2, 6]
def baseStart_4101333 : Nat := 118140960795 + 4101333 * 2 ^ 59
def prefixEnd_4101333 : Nat := 4983230072969 + 3 ^ 40 * 4101333 * 2
def baseEnd_4101333 : Nat := 233995017016278583275091

theorem tailTrace_4101333 : CollatzResearch.WordTrace tailWord_4101333 prefixEnd_4101333 233995017016278583275091 := by
  unfold tailWord_4101333
  simp only [CollatzResearch.WordTrace]
  refine ⟨149587903650578467755684653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99725269100385645170456435 149587903650578467755684653)
  ·
    refine ⟨56095463868966925408381745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149587903650578467755684653 56095463868966925408381745)
    ·
      refine ⟨42071597901725194056286309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56095463868966925408381745 42071597901725194056286309)
      ·
        refine ⟨7888424606573473885553683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42071597901725194056286309 7888424606573473885553683)
        ·
          refine ⟨11832636909860210828330525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7888424606573473885553683 11832636909860210828330525)
          ·
            refine ⟨4437238841197579060623947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11832636909860210828330525 4437238841197579060623947)
            ·
              refine ⟨6655858261796368590935921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4437238841197579060623947 6655858261796368590935921)
              ·
                refine ⟨4991893696347276443201941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6655858261796368590935921 4991893696347276443201941)
                ·
                  refine ⟨233995017016278583275091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4991893696347276443201941 233995017016278583275091)
                  ·
                    rfl

theorem cell23_4101333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 2, 6].length) (baseStart_4101333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4101333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4101333 prefixEnd_4101333 := by exact prefixLift 4101333
  have htrace : WordTrace (prefixWord ++ tailWord_4101333) baseStart_4101333 baseEnd_4101333 := by
    simpa [prefixWord, tailWord_4101333, baseEnd_4101333] using wordTrace_append hprefix tailTrace_4101333
  have hstable : (prefixWord ++ tailWord_4101333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101333).length < 2 ^ (prefixWord ++ tailWord_4101333).sum := by decide
  have hdescent : baseEnd_4101333 < baseStart_4101333 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101369 : List Nat := [1, 2, 1, 3, 1, 1, 3, 2, 3, 1, 5]
def baseStart_4101369 : Nat := 118140960795 + 4101369 * 2 ^ 59
def prefixEnd_4101369 : Nat := 4983230072969 + 3 ^ 40 * 4101369 * 2
def baseEnd_4101369 : Nat := 2105973638450069108625653

theorem tailTrace_4101369 : CollatzResearch.WordTrace tailWord_4101369 prefixEnd_4101369 2105973638450069108625653 := by
  unfold tailWord_4101369
  simp only [CollatzResearch.WordTrace]
  refine ⟨149589216678448045903995161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99726144452298697269330107 149589216678448045903995161)
  ·
    refine ⟨112191912508836034427996371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149589216678448045903995161 112191912508836034427996371)
    ·
      refine ⟨168287868763254051641994557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112191912508836034427996371 168287868763254051641994557)
      ·
        refine ⟨63107950786220269365747959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168287868763254051641994557 63107950786220269365747959)
        ·
          refine ⟨94661926179330404048621939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63107950786220269365747959 94661926179330404048621939)
          ·
            refine ⟨141992889268995606072932909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94661926179330404048621939 141992889268995606072932909)
            ·
              refine ⟨53247333475873352277349841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141992889268995606072932909 53247333475873352277349841)
              ·
                refine ⟨39935500106905014208012381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53247333475873352277349841 39935500106905014208012381)
                ·
                  refine ⟨14975812540089380328004643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39935500106905014208012381 14975812540089380328004643)
                  ·
                    refine ⟨22463718810134070492006965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14975812540089380328004643 22463718810134070492006965)
                    ·
                      refine ⟨2105973638450069108625653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22463718810134070492006965 2105973638450069108625653)
                      ·
                        rfl

theorem cell23_4101369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 3, 1, 5].length) (baseStart_4101369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4101369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4101369 prefixEnd_4101369 := by exact prefixLift 4101369
  have htrace : WordTrace (prefixWord ++ tailWord_4101369) baseStart_4101369 baseEnd_4101369 := by
    simpa [prefixWord, tailWord_4101369, baseEnd_4101369] using wordTrace_append hprefix tailTrace_4101369
  have hstable : (prefixWord ++ tailWord_4101369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101369).length < 2 ^ (prefixWord ++ tailWord_4101369).sum := by decide
  have hdescent : baseEnd_4101369 < baseStart_4101369 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101377 : List Nat := [1, 2, 4, 1, 1, 5, 1, 3, 1, 1, 3]
def baseStart_4101377 : Nat := 118140960795 + 4101377 * 2 ^ 59
def prefixEnd_4101377 : Nat := 4983230072969 + 3 ^ 40 * 4101377 * 2
def baseEnd_4101377 : Nat := 2105977746295305077325617

theorem tailTrace_4101377 : CollatzResearch.WordTrace tailWord_4101377 prefixEnd_4101377 2105977746295305077325617 := by
  unfold tailWord_4101377
  simp only [CollatzResearch.WordTrace]
  refine ⟨149589508462419063270286385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99726338974946042180190923 149589508462419063270286385)
  ·
    refine ⟨112192131346814297452714789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149589508462419063270286385 112192131346814297452714789)
    ·
      refine ⟨21036024627527680772384023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112192131346814297452714789 21036024627527680772384023)
      ·
        refine ⟨31554036941291521158576035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21036024627527680772384023 31554036941291521158576035)
        ·
          refine ⟨47331055411937281737864053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31554036941291521158576035 47331055411937281737864053)
          ·
            refine ⟨4437286444869120162924755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47331055411937281737864053 4437286444869120162924755)
            ·
              refine ⟨6655929667303680244387133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4437286444869120162924755 6655929667303680244387133)
              ·
                refine ⟨2495973625238880091645175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6655929667303680244387133 2495973625238880091645175)
                ·
                  refine ⟨3743960437858320137467763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2495973625238880091645175 3743960437858320137467763)
                  ·
                    refine ⟨5615940656787480206201645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3743960437858320137467763 5615940656787480206201645)
                    ·
                      refine ⟨2105977746295305077325617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5615940656787480206201645 2105977746295305077325617)
                      ·
                        rfl

theorem cell23_4101377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 3, 1, 1, 3].length) (baseStart_4101377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4101377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4101377 prefixEnd_4101377 := by exact prefixLift 4101377
  have htrace : WordTrace (prefixWord ++ tailWord_4101377) baseStart_4101377 baseEnd_4101377 := by
    simpa [prefixWord, tailWord_4101377, baseEnd_4101377] using wordTrace_append hprefix tailTrace_4101377
  have hstable : (prefixWord ++ tailWord_4101377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101377).length < 2 ^ (prefixWord ++ tailWord_4101377).sum := by decide
  have hdescent : baseEnd_4101377 < baseStart_4101377 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101386 : List Nat := [3, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3]
def baseStart_4101386 : Nat := 118140960795 + 4101386 * 2 ^ 59
def prefixEnd_4101386 : Nat := 4983230072969 + 3 ^ 40 * 4101386 * 2
def baseEnd_4101386 : Nat := 2105982367621195542113075

theorem tailTrace_4101386 : CollatzResearch.WordTrace tailWord_4101386 prefixEnd_4101386 2105982367621195542113075 := by
  unfold tailWord_4101386
  simp only [CollatzResearch.WordTrace]
  refine ⟨37397459179846614451841003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99726557812924305204909341 37397459179846614451841003)
  ·
    refine ⟨56096188769769921677761505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37397459179846614451841003 56096188769769921677761505)
    ·
      refine ⟨42072141577327441258321129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56096188769769921677761505 42072141577327441258321129)
      ·
        refine ⟨31554106182995580943740847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42072141577327441258321129 31554106182995580943740847)
        ·
          refine ⟨47331159274493371415611271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31554106182995580943740847 47331159274493371415611271)
          ·
            refine ⟨70996738911740057123416907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47331159274493371415611271 70996738911740057123416907)
            ·
              refine ⟨106495108367610085685125361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70996738911740057123416907 106495108367610085685125361)
              ·
                refine ⟨79871331275707564263844021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106495108367610085685125361 79871331275707564263844021)
                ·
                  refine ⟨7487937307097584149735377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79871331275707564263844021 7487937307097584149735377)
                  ·
                    refine ⟨5615952980323188112301533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7487937307097584149735377 5615952980323188112301533)
                    ·
                      refine ⟨2105982367621195542113075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5615952980323188112301533 2105982367621195542113075)
                      ·
                        rfl

theorem cell23_4101386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3].length) (baseStart_4101386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4101386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4101386 prefixEnd_4101386 := by exact prefixLift 4101386
  have htrace : WordTrace (prefixWord ++ tailWord_4101386) baseStart_4101386 baseEnd_4101386 := by
    simpa [prefixWord, tailWord_4101386, baseEnd_4101386] using wordTrace_append hprefix tailTrace_4101386
  have hstable : (prefixWord ++ tailWord_4101386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101386).length < 2 ^ (prefixWord ++ tailWord_4101386).sum := by decide
  have hdescent : baseEnd_4101386 < baseStart_4101386 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101394 : List Nat := [3, 2, 4, 2, 1, 2, 1, 1, 3, 1, 3]
def baseStart_4101394 : Nat := 118140960795 + 4101394 * 2 ^ 59
def prefixEnd_4101394 : Nat := 4983230072969 + 3 ^ 40 * 4101394 * 2
def baseEnd_4101394 : Nat := 2105986475466431510813039

theorem tailTrace_4101394 : CollatzResearch.WordTrace tailWord_4101394 prefixEnd_4101394 2105986475466431510813039 := by
  unfold tailWord_4101394
  simp only [CollatzResearch.WordTrace]
  refine ⟨37397532125839368793413809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99726752335571650115770157 37397532125839368793413809)
  ·
    refine ⟨28048149094379526595060357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37397532125839368793413809 28048149094379526595060357)
    ·
      refine ⟨5259027955196161236573817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28048149094379526595060357 5259027955196161236573817)
      ·
        refine ⟨3944270966397120927430363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5259027955196161236573817 3944270966397120927430363)
        ·
          refine ⟨5916406449595681391145545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3944270966397120927430363 5916406449595681391145545)
          ·
            refine ⟨4437304837196761043359159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5916406449595681391145545 4437304837196761043359159)
            ·
              refine ⟨6655957255795141565038739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4437304837196761043359159 6655957255795141565038739)
              ·
                refine ⟨9983935883692712347558109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6655957255795141565038739 9983935883692712347558109)
                ·
                  refine ⟨3743975956384767130334291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9983935883692712347558109 3743975956384767130334291)
                  ·
                    refine ⟨5615963934577150695501437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3743975956384767130334291 5615963934577150695501437)
                    ·
                      refine ⟨2105986475466431510813039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5615963934577150695501437 2105986475466431510813039)
                      ·
                        rfl

theorem cell23_4101394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_4101394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4101394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4101394 prefixEnd_4101394 := by exact prefixLift 4101394
  have htrace : WordTrace (prefixWord ++ tailWord_4101394) baseStart_4101394 baseEnd_4101394 := by
    simpa [prefixWord, tailWord_4101394, baseEnd_4101394] using wordTrace_append hprefix tailTrace_4101394
  have hstable : (prefixWord ++ tailWord_4101394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101394).length < 2 ^ (prefixWord ++ tailWord_4101394).sum := by decide
  have hdescent : baseEnd_4101394 < baseStart_4101394 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101400 : List Nat := [2, 1, 2, 3, 1, 3, 3, 1, 3, 2, 2]
def baseStart_4101400 : Nat := 118140960795 + 4101400 * 2 ^ 59
def prefixEnd_4101400 : Nat := 4983230072969 + 3 ^ 40 * 4101400 * 2
def baseEnd_4101400 : Nat := 2105989556350358487338011

theorem tailTrace_4101400 : CollatzResearch.WordTrace tailWord_4101400 prefixEnd_4101400 2105989556350358487338011 := by
  unfold tailWord_4101400
  simp only [CollatzResearch.WordTrace]
  refine ⟨74795173670667869099186827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99726898227557158798915769 74795173670667869099186827)
  ·
    refine ⟨112192760506001803648780241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74795173670667869099186827 112192760506001803648780241)
    ·
      refine ⟨84144570379501352736585181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112192760506001803648780241 84144570379501352736585181)
      ·
        refine ⟨31554213892313007276219443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84144570379501352736585181 31554213892313007276219443)
        ·
          refine ⟨47331320838469510914329165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31554213892313007276219443 47331320838469510914329165)
          ·
            refine ⟨17749245314426066592873437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47331320838469510914329165 17749245314426066592873437)
            ·
              refine ⟨6655966992909774972327539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17749245314426066592873437 6655966992909774972327539)
              ·
                refine ⟨9983950489364662458491309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6655966992909774972327539 9983950489364662458491309)
                ·
                  refine ⟨3743981433511748421934241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9983950489364662458491309 3743981433511748421934241)
                  ·
                    refine ⟨2807986075133811316450681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3743981433511748421934241 2807986075133811316450681)
                    ·
                      refine ⟨2105989556350358487338011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2807986075133811316450681 2105989556350358487338011)
                      ·
                        rfl

theorem cell23_4101400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 1, 3, 2, 2].length) (baseStart_4101400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4101400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4101400 prefixEnd_4101400 := by exact prefixLift 4101400
  have htrace : WordTrace (prefixWord ++ tailWord_4101400) baseStart_4101400 baseEnd_4101400 := by
    simpa [prefixWord, tailWord_4101400, baseEnd_4101400] using wordTrace_append hprefix tailTrace_4101400
  have hstable : (prefixWord ++ tailWord_4101400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101400).length < 2 ^ (prefixWord ++ tailWord_4101400).sum := by decide
  have hdescent : baseEnd_4101400 < baseStart_4101400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101409 : List Nat := [1, 2, 3, 2, 1, 1, 1, 1, 1, 4, 6]
def baseStart_4101409 : Nat := 118140960795 + 4101409 * 2 ^ 59
def prefixEnd_4101409 : Nat := 4983230072969 + 3 ^ 40 * 4101409 * 2
def baseEnd_4101409 : Nat := 2105994177676248952125469

theorem tailTrace_4101409 : CollatzResearch.WordTrace tailWord_4101409 prefixEnd_4101409 2105994177676248952125469 := by
  unfold tailWord_4101409
  simp only [CollatzResearch.WordTrace]
  refine ⟨149590675598303132735451281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99727117065535421823634187 149590675598303132735451281)
  ·
    refine ⟨112193006698727349551588461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149590675598303132735451281 112193006698727349551588461)
    ·
      refine ⟨42072377512022756081845673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112193006698727349551588461 42072377512022756081845673)
      ·
        refine ⟨31554283134017067061384255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42072377512022756081845673 31554283134017067061384255)
        ·
          refine ⟨47331424701025600592076383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31554283134017067061384255 47331424701025600592076383)
          ·
            refine ⟨70997137051538400888114575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47331424701025600592076383 70997137051538400888114575)
            ·
              refine ⟨106495705577307601332171863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70997137051538400888114575 106495705577307601332171863)
              ·
                refine ⟨159743558365961401998257795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106495705577307601332171863 159743558365961401998257795)
                ·
                  refine ⟨239615337548942102997386693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 159743558365961401998257795 239615337548942102997386693)
                  ·
                    refine ⟨44927875790426644312010005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 239615337548942102997386693 44927875790426644312010005)
                    ·
                      refine ⟨2105994177676248952125469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44927875790426644312010005 2105994177676248952125469)
                      ·
                        rfl

theorem cell23_4101409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_4101409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4101409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4101409 prefixEnd_4101409 := by exact prefixLift 4101409
  have htrace : WordTrace (prefixWord ++ tailWord_4101409) baseStart_4101409 baseEnd_4101409 := by
    simpa [prefixWord, tailWord_4101409, baseEnd_4101409] using wordTrace_append hprefix tailTrace_4101409
  have hstable : (prefixWord ++ tailWord_4101409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101409).length < 2 ^ (prefixWord ++ tailWord_4101409).sum := by decide
  have hdescent : baseEnd_4101409 < baseStart_4101409 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101410 : List Nat := [3, 3, 1, 1, 4, 1, 1, 3, 2, 4]
def baseStart_4101410 : Nat := 118140960795 + 4101410 * 2 ^ 59
def prefixEnd_4101410 : Nat := 4983230072969 + 3 ^ 40 * 4101410 * 2
def baseEnd_4101410 : Nat := 701998230385634482737655

theorem tailTrace_4101410 : CollatzResearch.WordTrace tailWord_4101410 prefixEnd_4101410 701998230385634482737655 := by
  unfold tailWord_4101410
  simp only [CollatzResearch.WordTrace]
  refine ⟨37397678017824877476559421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99727141380866339937491789 37397678017824877476559421)
  ·
    refine ⟨14024129256684329053709783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37397678017824877476559421 14024129256684329053709783)
    ·
      refine ⟨21036193885026493580564675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14024129256684329053709783 21036193885026493580564675)
      ·
        refine ⟨31554290827539740370847013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21036193885026493580564675 31554290827539740370847013)
        ·
          refine ⟨5916429530163701319533815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31554290827539740370847013 5916429530163701319533815)
          ·
            refine ⟨8874644295245551979300723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5916429530163701319533815 8874644295245551979300723)
            ·
              refine ⟨13311966442868327968951085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8874644295245551979300723 13311966442868327968951085)
              ·
                refine ⟨4991987416075622988356657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13311966442868327968951085 4991987416075622988356657)
                ·
                  refine ⟨3743990562056717241267493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4991987416075622988356657 3743990562056717241267493)
                  ·
                    refine ⟨701998230385634482737655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3743990562056717241267493 701998230385634482737655)
                    ·
                      rfl

theorem cell23_4101410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 3, 2, 4].length) (baseStart_4101410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4101410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4101410 prefixEnd_4101410 := by exact prefixLift 4101410
  have htrace : WordTrace (prefixWord ++ tailWord_4101410) baseStart_4101410 baseEnd_4101410 := by
    simpa [prefixWord, tailWord_4101410, baseEnd_4101410] using wordTrace_append hprefix tailTrace_4101410
  have hstable : (prefixWord ++ tailWord_4101410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101410).length < 2 ^ (prefixWord ++ tailWord_4101410).sum := by decide
  have hdescent : baseEnd_4101410 < baseStart_4101410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101437 : List Nat := [1, 4, 1, 5, 2, 1, 1, 1, 1, 1, 5]
def baseStart_4101437 : Nat := 118140960795 + 4101437 * 2 ^ 59
def prefixEnd_4101437 : Nat := 4983230072969 + 3 ^ 40 * 4101437 * 2
def baseEnd_4101437 : Nat := 2106008555134574842575341

theorem tailTrace_4101437 : CollatzResearch.WordTrace tailWord_4101437 prefixEnd_4101437 2106008555134574842575341 := by
  unfold tailWord_4101437
  simp only [CollatzResearch.WordTrace]
  refine ⟨149591696842201693517470565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99727797894801129011647043 149591696842201693517470565)
  ·
    refine ⟨28048443157912817534525731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149591696842201693517470565 28048443157912817534525731)
    ·
      refine ⟨42072664736869226301788597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28048443157912817534525731 42072664736869226301788597)
      ·
        refine ⟨3944312319081489965792681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42072664736869226301788597 3944312319081489965792681)
        ·
          refine ⟨2958234239311117474344511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3944312319081489965792681 2958234239311117474344511)
          ·
            refine ⟨4437351358966676211516767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2958234239311117474344511 4437351358966676211516767)
            ·
              refine ⟨6656027038450014317275151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4437351358966676211516767 6656027038450014317275151)
              ·
                refine ⟨9984040557675021475912727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6656027038450014317275151 9984040557675021475912727)
                ·
                  refine ⟨14976060836512532213869091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9984040557675021475912727 14976060836512532213869091)
                  ·
                    refine ⟨22464091254768798320803637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14976060836512532213869091 22464091254768798320803637)
                    ·
                      refine ⟨2106008555134574842575341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22464091254768798320803637 2106008555134574842575341)
                      ·
                        rfl

theorem cell23_4101437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_4101437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4101437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4101437 prefixEnd_4101437 := by exact prefixLift 4101437
  have htrace : WordTrace (prefixWord ++ tailWord_4101437) baseStart_4101437 baseEnd_4101437 := by
    simpa [prefixWord, tailWord_4101437, baseEnd_4101437] using wordTrace_append hprefix tailTrace_4101437
  have hstable : (prefixWord ++ tailWord_4101437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101437).length < 2 ^ (prefixWord ++ tailWord_4101437).sum := by decide
  have hdescent : baseEnd_4101437 < baseStart_4101437 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101490 : List Nat := [3, 2, 1, 2, 1, 2, 2, 2, 4, 2, 2]
def baseStart_4101490 : Nat := 118140960795 + 4101490 * 2 ^ 59
def prefixEnd_4101490 : Nat := 4983230072969 + 3 ^ 40 * 4101490 * 2
def baseEnd_4101490 : Nat := 2106035769609263135212597

theorem tailTrace_4101490 : CollatzResearch.WordTrace tailWord_4101490 prefixEnd_4101490 2106035769609263135212597 := by
  unfold tailWord_4101490
  simp only [CollatzResearch.WordTrace]
  refine ⟨37398407477752420892287481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99729086607339789046099949 37398407477752420892287481)
  ·
    refine ⟨28048805608314315669215611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37398407477752420892287481 28048805608314315669215611)
    ·
      refine ⟨42073208412471473503823417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28048805608314315669215611 42073208412471473503823417)
      ·
        refine ⟨31554906309353605127867563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42073208412471473503823417 31554906309353605127867563)
        ·
          refine ⟨47332359464030407691801345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31554906309353605127867563 47332359464030407691801345)
          ·
            refine ⟨35499269598022805768851009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47332359464030407691801345 35499269598022805768851009)
            ·
              refine ⟨26624452198517104326638257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35499269598022805768851009 26624452198517104326638257)
              ·
                refine ⟨19968339148887828244978693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26624452198517104326638257 19968339148887828244978693)
                ·
                  refine ⟨3744063590416467795933505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19968339148887828244978693 3744063590416467795933505)
                  ·
                    refine ⟨2808047692812350846950129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3744063590416467795933505 2808047692812350846950129)
                    ·
                      refine ⟨2106035769609263135212597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2808047692812350846950129 2106035769609263135212597)
                      ·
                        rfl

theorem cell23_4101490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 4, 2, 2].length) (baseStart_4101490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4101490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4101490 prefixEnd_4101490 := by exact prefixLift 4101490
  have htrace : WordTrace (prefixWord ++ tailWord_4101490) baseStart_4101490 baseEnd_4101490 := by
    simpa [prefixWord, tailWord_4101490, baseEnd_4101490] using wordTrace_append hprefix tailTrace_4101490
  have hstable : (prefixWord ++ tailWord_4101490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101490).length < 2 ^ (prefixWord ++ tailWord_4101490).sum := by decide
  have hdescent : baseEnd_4101490 < baseStart_4101490 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101507 : List Nat := [1, 1, 1, 3, 5, 1, 3, 2, 2, 2, 2]
def baseStart_4101507 : Nat := 118140960795 + 4101507 * 2 ^ 59
def prefixEnd_4101507 : Nat := 4983230072969 + 3 ^ 40 * 4101507 * 2
def baseEnd_4101507 : Nat := 2106044498780389568700019

theorem tailTrace_4101507 : CollatzResearch.WordTrace tailWord_4101507 prefixEnd_4101507 2106044498780389568700019 := by
  unfold tailWord_4101507
  simp only [CollatzResearch.WordTrace]
  refine ⟨149594249951948095472518775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99729499967965396981679183 149594249951948095472518775)
  ·
    refine ⟨224391374927922143208778163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149594249951948095472518775 224391374927922143208778163)
    ·
      refine ⟨336587062391883214813167245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224391374927922143208778163 336587062391883214813167245)
      ·
        refine ⟨126220148396956205554937717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 336587062391883214813167245 126220148396956205554937717)
        ·
          refine ⟨11833138912214644270775411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 126220148396956205554937717 11833138912214644270775411)
          ·
            refine ⟨17749708368321966406163117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11833138912214644270775411 17749708368321966406163117)
            ·
              refine ⟨6656140638120737402311169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17749708368321966406163117 6656140638120737402311169)
              ·
                refine ⟨4992105478590553051733377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6656140638120737402311169 4992105478590553051733377)
                ·
                  refine ⟨3744079108942914788800033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4992105478590553051733377 3744079108942914788800033)
                  ·
                    refine ⟨2808059331707186091600025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3744079108942914788800033 2808059331707186091600025)
                    ·
                      refine ⟨2106044498780389568700019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2808059331707186091600025 2106044498780389568700019)
                      ·
                        rfl

theorem cell23_4101507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 2, 2, 2, 2].length) (baseStart_4101507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4101507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4101507 prefixEnd_4101507 := by exact prefixLift 4101507
  have htrace : WordTrace (prefixWord ++ tailWord_4101507) baseStart_4101507 baseEnd_4101507 := by
    simpa [prefixWord, tailWord_4101507, baseEnd_4101507] using wordTrace_append hprefix tailTrace_4101507
  have hstable : (prefixWord ++ tailWord_4101507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101507).length < 2 ^ (prefixWord ++ tailWord_4101507).sum := by decide
  have hdescent : baseEnd_4101507 < baseStart_4101507 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101513 : List Nat := [1, 2, 1, 1, 7, 1, 2, 1, 7]
def baseStart_4101513 : Nat := 118140960795 + 4101513 * 2 ^ 59
def prefixEnd_4101513 : Nat := 4983230072969 + 3 ^ 40 * 4101513 * 2
def baseEnd_4101513 : Nat := 234005286629368505024999

theorem tailTrace_4101513 : CollatzResearch.WordTrace tailWord_4101513 prefixEnd_4101513 234005286629368505024999 := by
  unfold tailWord_4101513
  simp only [CollatzResearch.WordTrace]
  refine ⟨149594468789926358497237193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99729645859950905664824795 149594468789926358497237193)
  ·
    refine ⟨112195851592444768872927895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149594468789926358497237193 112195851592444768872927895)
    ·
      refine ⟨168293777388667153309391843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112195851592444768872927895 168293777388667153309391843)
      ·
        refine ⟨252440666083000729964087765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168293777388667153309391843 252440666083000729964087765)
        ·
          refine ⟨5916578111320329608533307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 252440666083000729964087765 5916578111320329608533307)
          ·
            refine ⟨8874867166980494412799961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5916578111320329608533307 8874867166980494412799961)
            ·
              refine ⟨6656150375235370809599971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8874867166980494412799961 6656150375235370809599971)
              ·
                refine ⟨9984225562853056214399957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6656150375235370809599971 9984225562853056214399957)
                ·
                  refine ⟨234005286629368505024999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9984225562853056214399957 234005286629368505024999)
                  ·
                    rfl

theorem cell23_4101513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 1, 7].length) (baseStart_4101513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4101513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4101513 prefixEnd_4101513 := by exact prefixLift 4101513
  have htrace : WordTrace (prefixWord ++ tailWord_4101513) baseStart_4101513 baseEnd_4101513 := by
    simpa [prefixWord, tailWord_4101513, baseEnd_4101513] using wordTrace_append hprefix tailTrace_4101513
  have hstable : (prefixWord ++ tailWord_4101513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101513).length < 2 ^ (prefixWord ++ tailWord_4101513).sum := by decide
  have hdescent : baseEnd_4101513 < baseStart_4101513 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101543 : List Nat := [1, 1, 6, 1, 1, 1, 2, 3, 2, 5]
def baseStart_4101543 : Nat := 118140960795 + 4101543 * 2 ^ 59
def prefixEnd_4101543 : Nat := 4983230072969 + 3 ^ 40 * 4101543 * 2
def baseEnd_4101543 : Nat := 702020994694650475949951

theorem tailTrace_4101543 : CollatzResearch.WordTrace tailWord_4101543 prefixEnd_4101543 702020994694650475949951 := by
  unfold tailWord_4101543
  simp only [CollatzResearch.WordTrace]
  refine ⟨149595562979817673620829283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99730375319878449080552855 149595562979817673620829283)
  ·
    refine ⟨224393344469726510431243925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149595562979817673620829283 224393344469726510431243925)
    ·
      refine ⟨10518438022018430176464559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 224393344469726510431243925 10518438022018430176464559)
      ·
        refine ⟨15777657033027645264696839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10518438022018430176464559 15777657033027645264696839)
        ·
          refine ⟨23666485549541467897045259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15777657033027645264696839 23666485549541467897045259)
          ·
            refine ⟨35499728324312201845567889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23666485549541467897045259 35499728324312201845567889)
            ·
              refine ⟨26624796243234151384175917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35499728324312201845567889 26624796243234151384175917)
              ·
                refine ⟨9984298591212806769065969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26624796243234151384175917 9984298591212806769065969)
                ·
                  refine ⟨7488223943409605076799477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9984298591212806769065969 7488223943409605076799477)
                  ·
                    refine ⟨702020994694650475949951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7488223943409605076799477 702020994694650475949951)
                    ·
                      rfl

theorem cell23_4101543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_4101543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4101543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4101543 prefixEnd_4101543 := by exact prefixLift 4101543
  have htrace : WordTrace (prefixWord ++ tailWord_4101543) baseStart_4101543 baseEnd_4101543 := by
    simpa [prefixWord, tailWord_4101543, baseEnd_4101543] using wordTrace_append hprefix tailTrace_4101543
  have hstable : (prefixWord ++ tailWord_4101543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101543).length < 2 ^ (prefixWord ++ tailWord_4101543).sum := by decide
  have hdescent : baseEnd_4101543 < baseStart_4101543 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101624 : List Nat := [2, 1, 2, 1, 1, 7, 2, 2, 1, 4]
def baseStart_4101624 : Nat := 118140960795 + 4101624 * 2 ^ 59
def prefixEnd_4101624 : Nat := 4983230072969 + 3 ^ 40 * 4101624 * 2
def baseEnd_4101624 : Nat := 702034858672321870312327

theorem tailTrace_4101624 : CollatzResearch.WordTrace tailWord_4101624 prefixEnd_4101624 702034858672321870312327 := by
  unfold tailWord_4101624
  simp only [CollatzResearch.WordTrace]
  refine ⟨74799258646262112227263963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99732344861682816303018617 74799258646262112227263963)
  ·
    refine ⟨112198887969393168340895945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74799258646262112227263963 112198887969393168340895945)
    ·
      refine ⟨84149165977044876255671959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112198887969393168340895945 84149165977044876255671959)
      ·
        refine ⟨126223748965567314383507939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84149165977044876255671959 126223748965567314383507939)
        ·
          refine ⟨189335623448350971575261909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126223748965567314383507939 189335623448350971575261909)
          ·
            refine ⟨4437553674570725896295201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 189335623448350971575261909 4437553674570725896295201)
            ·
              refine ⟨3328165255928044422221401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4437553674570725896295201 3328165255928044422221401)
              ·
                refine ⟨2496123941946033316666051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3328165255928044422221401 2496123941946033316666051)
                ·
                  refine ⟨3744185912919049974999077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2496123941946033316666051 3744185912919049974999077)
                  ·
                    refine ⟨702034858672321870312327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3744185912919049974999077 702034858672321870312327)
                    ·
                      rfl

theorem cell23_4101624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 2, 2, 1, 4].length) (baseStart_4101624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4101624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4101624 prefixEnd_4101624 := by exact prefixLift 4101624
  have htrace : WordTrace (prefixWord ++ tailWord_4101624) baseStart_4101624 baseEnd_4101624 := by
    simpa [prefixWord, tailWord_4101624, baseEnd_4101624] using wordTrace_append hprefix tailTrace_4101624
  have hstable : (prefixWord ++ tailWord_4101624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101624).length < 2 ^ (prefixWord ++ tailWord_4101624).sum := by decide
  have hdescent : baseEnd_4101624 < baseStart_4101624 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101640 : List Nat := [2, 1, 3, 2, 1, 1, 2, 2, 4, 3, 2]
def baseStart_4101640 : Nat := 118140960795 + 4101640 * 2 ^ 59
def prefixEnd_4101640 : Nat := 4983230072969 + 3 ^ 40 * 4101640 * 2
def baseEnd_4101640 : Nat := 2106112791707437548336907

theorem tailTrace_4101640 : CollatzResearch.WordTrace tailWord_4101640 prefixEnd_4101640 2106112791707437548336907 := by
  unfold tailWord_4101640
  simp only [CollatzResearch.WordTrace]
  refine ⟨74799550430233129593555187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99732733906977506124740249 74799550430233129593555187)
  ·
    refine ⟨112199325645349694390332781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74799550430233129593555187 112199325645349694390332781)
    ·
      refine ⟨42074747117006135396374793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112199325645349694390332781 42074747117006135396374793)
      ·
        refine ⟨31556060337754601547281095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42074747117006135396374793 31556060337754601547281095)
        ·
          refine ⟨47334090506631902320921643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31556060337754601547281095 47334090506631902320921643)
          ·
            refine ⟨71001135759947853481382465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47334090506631902320921643 71001135759947853481382465)
            ·
              refine ⟨53250851819960890111036849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71001135759947853481382465 53250851819960890111036849)
              ·
                refine ⟨39938138864970667583277637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53250851819960890111036849 39938138864970667583277637)
                ·
                  refine ⟨7488401037182000171864557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39938138864970667583277637 7488401037182000171864557)
                  ·
                    refine ⟨2808150388943250064449209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7488401037182000171864557 2808150388943250064449209)
                    ·
                      refine ⟨2106112791707437548336907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2808150388943250064449209 2106112791707437548336907)
                      ·
                        rfl

theorem cell23_4101640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 4, 3, 2].length) (baseStart_4101640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4101640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4101640 prefixEnd_4101640 := by exact prefixLift 4101640
  have htrace : WordTrace (prefixWord ++ tailWord_4101640) baseStart_4101640 baseEnd_4101640 := by
    simpa [prefixWord, tailWord_4101640, baseEnd_4101640] using wordTrace_append hprefix tailTrace_4101640
  have hstable : (prefixWord ++ tailWord_4101640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101640).length < 2 ^ (prefixWord ++ tailWord_4101640).sum := by decide
  have hdescent : baseEnd_4101640 < baseStart_4101640 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101663 : List Nat := [1, 1, 2, 4, 1, 1, 4, 2, 1, 6]
def baseStart_4101663 : Nat := 118140960795 + 4101663 * 2 ^ 59
def prefixEnd_4101663 : Nat := 4983230072969 + 3 ^ 40 * 4101663 * 2
def baseEnd_4101663 : Nat := 702041533920830319449767

theorem tailTrace_4101663 : CollatzResearch.WordTrace tailWord_4101663 prefixEnd_4101663 702041533920830319449767 := by
  unfold tailWord_4101663
  simp only [CollatzResearch.WordTrace]
  refine ⟨149599939739382934115197643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99733293159588622743465095 149599939739382934115197643)
  ·
    refine ⟨224399909609074401172796465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149599939739382934115197643 224399909609074401172796465)
    ·
      refine ⟨168299932206805800879597349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224399909609074401172796465 168299932206805800879597349)
      ·
        refine ⟨31556237288776087664924503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168299932206805800879597349 31556237288776087664924503)
        ·
          refine ⟨47334355933164131497386755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31556237288776087664924503 47334355933164131497386755)
          ·
            refine ⟨71001533899746197246080133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47334355933164131497386755 71001533899746197246080133)
            ·
              refine ⟨13312787606202411983640025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71001533899746197246080133 13312787606202411983640025)
              ·
                refine ⟨9984590704651808987730019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13312787606202411983640025 9984590704651808987730019)
                ·
                  refine ⟨14976886056977713481595029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9984590704651808987730019 14976886056977713481595029)
                  ·
                    refine ⟨702041533920830319449767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14976886056977713481595029 702041533920830319449767)
                    ·
                      rfl

theorem cell23_4101663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 2, 1, 6].length) (baseStart_4101663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4101663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4101663 prefixEnd_4101663 := by exact prefixLift 4101663
  have htrace : WordTrace (prefixWord ++ tailWord_4101663) baseStart_4101663 baseEnd_4101663 := by
    simpa [prefixWord, tailWord_4101663, baseEnd_4101663] using wordTrace_append hprefix tailTrace_4101663
  have hstable : (prefixWord ++ tailWord_4101663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101663).length < 2 ^ (prefixWord ++ tailWord_4101663).sum := by decide
  have hdescent : baseEnd_4101663 < baseStart_4101663 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101664 : List Nat := [2, 1, 1, 6, 1, 1, 1, 5, 1, 1, 3]
def baseStart_4101664 : Nat := 118140960795 + 4101664 * 2 ^ 59
def prefixEnd_4101664 : Nat := 4983230072969 + 3 ^ 40 * 4101664 * 2
def baseEnd_4101664 : Nat := 2106125115243145454436797

theorem tailTrace_4101664 : CollatzResearch.WordTrace tailWord_4101664 prefixEnd_4101664 2106125115243145454436797 := by
  unfold tailWord_4101664
  simp only [CollatzResearch.WordTrace]
  refine ⟨74799988106189655642992023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99733317474919540857322697 74799988106189655642992023)
  ·
    refine ⟨112199982159284483464488035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74799988106189655642992023 112199982159284483464488035)
    ·
      refine ⟨168299973238926725196732053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112199982159284483464488035 168299973238926725196732053)
      ·
        refine ⟨7889061245574690243596815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 168299973238926725196732053 7889061245574690243596815)
        ·
          refine ⟨11833591868362035365395223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7889061245574690243596815 11833591868362035365395223)
          ·
            refine ⟨17750387802543053048092835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11833591868362035365395223 17750387802543053048092835)
            ·
              refine ⟨26625581703814579572139253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17750387802543053048092835 26625581703814579572139253)
              ·
                refine ⟨2496148284732616834888055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26625581703814579572139253 2496148284732616834888055)
                ·
                  refine ⟨3744222427098925252332083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2496148284732616834888055 3744222427098925252332083)
                  ·
                    refine ⟨5616333640648387878498125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3744222427098925252332083 5616333640648387878498125)
                    ·
                      refine ⟨2106125115243145454436797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5616333640648387878498125 2106125115243145454436797)
                      ·
                        rfl

theorem cell23_4101664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_4101664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4101664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4101664 prefixEnd_4101664 := by exact prefixLift 4101664
  have htrace : WordTrace (prefixWord ++ tailWord_4101664) baseStart_4101664 baseEnd_4101664 := by
    simpa [prefixWord, tailWord_4101664, baseEnd_4101664] using wordTrace_append hprefix tailTrace_4101664
  have hstable : (prefixWord ++ tailWord_4101664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101664).length < 2 ^ (prefixWord ++ tailWord_4101664).sum := by decide
  have hdescent : baseEnd_4101664 < baseStart_4101664 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101687 : List Nat := [1, 1, 3, 1, 2, 4, 1, 3, 3, 2, 2]
def baseStart_4101687 : Nat := 118140960795 + 4101687 * 2 ^ 59
def prefixEnd_4101687 : Nat := 4983230072969 + 3 ^ 40 * 4101687 * 2
def baseEnd_4101687 : Nat := 2106136925298198864449191

theorem tailTrace_4101687 : CollatzResearch.WordTrace tailWord_4101687 prefixEnd_4101687 2106136925298198864449191 := by
  unfold tailWord_4101687
  simp only [CollatzResearch.WordTrace]
  refine ⟨149600815091295986214071315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99733876727530657476047543 149600815091295986214071315)
  ·
    refine ⟨224401222636943979321106973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149600815091295986214071315 224401222636943979321106973)
    ·
      refine ⟨84150458488853992245415115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224401222636943979321106973 84150458488853992245415115)
      ·
        refine ⟨126225687733280988368122673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84150458488853992245415115 126225687733280988368122673)
        ·
          refine ⟨94669265799960741276092005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126225687733280988368122673 94669265799960741276092005)
          ·
            refine ⟨17750487337492638989267251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94669265799960741276092005 17750487337492638989267251)
            ·
              refine ⟨26625731006238958483900877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17750487337492638989267251 26625731006238958483900877)
              ·
                refine ⟨9984649127339609431462829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26625731006238958483900877 9984649127339609431462829)
                ·
                  refine ⟨3744243422752353536798561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9984649127339609431462829 3744243422752353536798561)
                  ·
                    refine ⟨2808182567064265152598921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3744243422752353536798561 2808182567064265152598921)
                    ·
                      refine ⟨2106136925298198864449191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2808182567064265152598921 2106136925298198864449191)
                      ·
                        rfl

theorem cell23_4101687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 3, 3, 2, 2].length) (baseStart_4101687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4101687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4101687 prefixEnd_4101687 := by exact prefixLift 4101687
  have htrace : WordTrace (prefixWord ++ tailWord_4101687) baseStart_4101687 baseEnd_4101687 := by
    simpa [prefixWord, tailWord_4101687, baseEnd_4101687] using wordTrace_append hprefix tailTrace_4101687
  have hstable : (prefixWord ++ tailWord_4101687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101687).length < 2 ^ (prefixWord ++ tailWord_4101687).sum := by decide
  have hdescent : baseEnd_4101687 < baseStart_4101687 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101738 : List Nat := [3, 1, 3, 2, 1, 3, 3, 2, 1, 2, 2]
def baseStart_4101738 : Nat := 118140960795 + 4101738 * 2 ^ 59
def prefixEnd_4101738 : Nat := 4983230072969 + 3 ^ 40 * 4101738 * 2
def baseEnd_4101738 : Nat := 2106163112811578164911457

theorem tailTrace_4101738 : CollatzResearch.WordTrace tailWord_4101738 prefixEnd_4101738 2106163112811578164911457 := by
  unfold tailWord_4101738
  simp only [CollatzResearch.WordTrace]
  refine ⟨37400668803527805481044467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99735116809407481282785245 37400668803527805481044467)
  ·
    refine ⟨56101003205291708221566701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37400668803527805481044467 56101003205291708221566701)
    ·
      refine ⟨21037876201984390583087513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56101003205291708221566701 21037876201984390583087513)
      ·
        refine ⟨15778407151488292937315635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21037876201984390583087513 15778407151488292937315635)
        ·
          refine ⟨23667610727232439405973453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15778407151488292937315635 23667610727232439405973453)
          ·
            refine ⟨8875354022712164777240045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23667610727232439405973453 8875354022712164777240045)
            ·
              refine ⟨3328257758517061791465017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8875354022712164777240045 3328257758517061791465017)
              ·
                refine ⟨2496193318887796343598763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3328257758517061791465017 2496193318887796343598763)
                ·
                  refine ⟨3744289978331694515398145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2496193318887796343598763 3744289978331694515398145)
                  ·
                    refine ⟨2808217483748770886548609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3744289978331694515398145 2808217483748770886548609)
                    ·
                      refine ⟨2106163112811578164911457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2808217483748770886548609 2106163112811578164911457)
                      ·
                        rfl

theorem cell23_4101738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 3, 2, 1, 2, 2].length) (baseStart_4101738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4101738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4101738 prefixEnd_4101738 := by exact prefixLift 4101738
  have htrace : WordTrace (prefixWord ++ tailWord_4101738) baseStart_4101738 baseEnd_4101738 := by
    simpa [prefixWord, tailWord_4101738, baseEnd_4101738] using wordTrace_append hprefix tailTrace_4101738
  have hstable : (prefixWord ++ tailWord_4101738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101738).length < 2 ^ (prefixWord ++ tailWord_4101738).sum := by decide
  have hdescent : baseEnd_4101738 < baseStart_4101738 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101743 : List Nat := [1, 1, 2, 1, 3, 2, 1, 3, 2, 3, 4]
def baseStart_4101743 : Nat := 118140960795 + 4101743 * 2 ^ 59
def prefixEnd_4101743 : Nat := 4983230072969 + 3 ^ 40 * 4101743 * 2
def baseEnd_4101743 : Nat := 2106165680214850645348933

theorem tailTrace_4101743 : CollatzResearch.WordTrace tailWord_4101743 prefixEnd_4101743 2106165680214850645348933 := by
  unfold tailWord_4101743
  simp only [CollatzResearch.WordTrace]
  refine ⟨149602857579093107778109883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99735238386062071852073255 149602857579093107778109883)
  ·
    refine ⟨224404286368639661667164825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149602857579093107778109883 224404286368639661667164825)
    ·
      refine ⟨168303214776479746250373619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224404286368639661667164825 168303214776479746250373619)
      ·
        refine ⟨252454822164719619375560429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168303214776479746250373619 252454822164719619375560429)
        ·
          refine ⟨94670558311769857265835161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252454822164719619375560429 94670558311769857265835161)
          ·
            refine ⟨71002918733827392949376371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94670558311769857265835161 71002918733827392949376371)
            ·
              refine ⟨106504378100741089424064557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71002918733827392949376371 106504378100741089424064557)
              ·
                refine ⟨39939141787777908534024209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106504378100741089424064557 39939141787777908534024209)
                ·
                  refine ⟨29954356340833431400518157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39939141787777908534024209 29954356340833431400518157)
                  ·
                    refine ⟨11232883627812536775194309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29954356340833431400518157 11232883627812536775194309)
                    ·
                      refine ⟨2106165680214850645348933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11232883627812536775194309 2106165680214850645348933)
                      ·
                        rfl

theorem cell23_4101743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 3, 4].length) (baseStart_4101743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4101743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4101743 prefixEnd_4101743 := by exact prefixLift 4101743
  have htrace : WordTrace (prefixWord ++ tailWord_4101743) baseStart_4101743 baseEnd_4101743 := by
    simpa [prefixWord, tailWord_4101743, baseEnd_4101743] using wordTrace_append hprefix tailTrace_4101743
  have hstable : (prefixWord ++ tailWord_4101743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101743).length < 2 ^ (prefixWord ++ tailWord_4101743).sum := by decide
  have hdescent : baseEnd_4101743 < baseStart_4101743 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101753 : List Nat := [1, 2, 1, 3, 3, 1, 2, 1, 1, 8]
def baseStart_4101753 : Nat := 118140960795 + 4101753 * 2 ^ 59
def prefixEnd_4101753 : Nat := 4983230072969 + 3 ^ 40 * 4101753 * 2
def baseEnd_4101753 : Nat := 702056938340465202074629

theorem tailTrace_4101753 : CollatzResearch.WordTrace tailWord_4101753 prefixEnd_4101753 702056938340465202074629 := by
  unfold tailWord_4101753
  simp only [CollatzResearch.WordTrace]
  refine ⟨149603222309056879485973913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99735481539371252990649275 149603222309056879485973913)
  ·
    refine ⟨112202416731792659614480435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149603222309056879485973913 112202416731792659614480435)
    ·
      refine ⟨168303625097688989421720653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112202416731792659614480435 168303625097688989421720653)
      ·
        refine ⟨63113859411633371033145245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168303625097688989421720653 63113859411633371033145245)
        ·
          refine ⟨23667697279362514137429467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63113859411633371033145245 23667697279362514137429467)
          ·
            refine ⟨35501545919043771206144201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23667697279362514137429467 35501545919043771206144201)
            ·
              refine ⟨26626159439282828404608151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35501545919043771206144201 26626159439282828404608151)
              ·
                refine ⟨39939239158924242606912227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26626159439282828404608151 39939239158924242606912227)
                ·
                  refine ⟨59908858738386363910368341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39939239158924242606912227 59908858738386363910368341)
                  ·
                    refine ⟨702056938340465202074629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 59908858738386363910368341 702056938340465202074629)
                    ·
                      rfl

theorem cell23_4101753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 8].length) (baseStart_4101753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4101753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4101753 prefixEnd_4101753 := by exact prefixLift 4101753
  have htrace : WordTrace (prefixWord ++ tailWord_4101753) baseStart_4101753 baseEnd_4101753 := by
    simpa [prefixWord, tailWord_4101753, baseEnd_4101753] using wordTrace_append hprefix tailTrace_4101753
  have hstable : (prefixWord ++ tailWord_4101753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101753).length < 2 ^ (prefixWord ++ tailWord_4101753).sum := by decide
  have hdescent : baseEnd_4101753 < baseStart_4101753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101764 : List Nat := [2, 3, 2, 1, 4, 1, 1, 1, 3, 3, 2]
def baseStart_4101764 : Nat := 118140960795 + 4101764 * 2 ^ 59
def prefixEnd_4101764 : Nat := 4983230072969 + 3 ^ 40 * 4101764 * 2
def baseEnd_4101764 : Nat := 2106176463308595063186337

theorem tailTrace_4101764 : CollatzResearch.WordTrace tailWord_4101764 prefixEnd_4101764 2106176463308595063186337 := by
  unfold tailWord_4101764
  simp only [CollatzResearch.WordTrace]
  refine ⟨74801811756008514182312173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99735749008011352243082897 74801811756008514182312173)
  ·
    refine ⟨28050679408503192818367065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74801811756008514182312173 28050679408503192818367065)
    ·
      refine ⟨21038009556377394613775299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28050679408503192818367065 21038009556377394613775299)
      ·
        refine ⟨31557014334566091920662949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21038009556377394613775299 31557014334566091920662949)
        ·
          refine ⟨5916940187731142235124303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31557014334566091920662949 5916940187731142235124303)
          ·
            refine ⟨8875410281596713352686455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5916940187731142235124303 8875410281596713352686455)
            ·
              refine ⟨13313115422395070029029683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8875410281596713352686455 13313115422395070029029683)
              ·
                refine ⟨19969673133592605043544525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13313115422395070029029683 19969673133592605043544525)
                ·
                  refine ⟨7488627425097226891329197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19969673133592605043544525 7488627425097226891329197)
                  ·
                    refine ⟨2808235284411460084248449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7488627425097226891329197 2808235284411460084248449)
                    ·
                      refine ⟨2106176463308595063186337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2808235284411460084248449 2106176463308595063186337)
                      ·
                        rfl

theorem cell23_4101764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 3, 3, 2].length) (baseStart_4101764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4101764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4101764 prefixEnd_4101764 := by exact prefixLift 4101764
  have htrace : WordTrace (prefixWord ++ tailWord_4101764) baseStart_4101764 baseEnd_4101764 := by
    simpa [prefixWord, tailWord_4101764, baseEnd_4101764] using wordTrace_append hprefix tailTrace_4101764
  have hstable : (prefixWord ++ tailWord_4101764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101764).length < 2 ^ (prefixWord ++ tailWord_4101764).sum := by decide
  have hdescent : baseEnd_4101764 < baseStart_4101764 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101777 : List Nat := [1, 2, 2, 1, 1, 1, 1, 6, 4, 2, 2]
def baseStart_4101777 : Nat := 118140960795 + 4101777 * 2 ^ 59
def prefixEnd_4101777 : Nat := 4983230072969 + 3 ^ 40 * 4101777 * 2
def baseEnd_4101777 : Nat := 2106183138557103512323777

theorem tailTrace_4101777 : CollatzResearch.WordTrace tailWord_4101777 prefixEnd_4101777 2106183138557103512323777 := by
  unfold tailWord_4101777
  simp only [CollatzResearch.WordTrace]
  refine ⟨149604097660969931584847585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99736065107313287723231723 149604097660969931584847585)
  ·
    refine ⟨112203073245727448688635689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149604097660969931584847585 112203073245727448688635689)
    ·
      refine ⟨84152304934295586516476767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112203073245727448688635689 84152304934295586516476767)
      ·
        refine ⟨126228457401443379774715151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84152304934295586516476767 126228457401443379774715151)
        ·
          refine ⟨189342686102165069662072727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126228457401443379774715151 189342686102165069662072727)
          ·
            refine ⟨284014029153247604493109091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189342686102165069662072727 284014029153247604493109091)
            ·
              refine ⟨426021043729871406739663637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284014029153247604493109091 426021043729871406739663637)
              ·
                refine ⟨19969736424837722190921733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 426021043729871406739663637 19969736424837722190921733)
                ·
                  refine ⟨3744325579657072910797825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19969736424837722190921733 3744325579657072910797825)
                  ·
                    refine ⟨2808244184742804683098369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3744325579657072910797825 2808244184742804683098369)
                    ·
                      refine ⟨2106183138557103512323777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2808244184742804683098369 2106183138557103512323777)
                      ·
                        rfl

theorem cell23_4101777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 4, 2, 2].length) (baseStart_4101777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4101777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4101777 prefixEnd_4101777 := by exact prefixLift 4101777
  have htrace : WordTrace (prefixWord ++ tailWord_4101777) baseStart_4101777 baseEnd_4101777 := by
    simpa [prefixWord, tailWord_4101777, baseEnd_4101777] using wordTrace_append hprefix tailTrace_4101777
  have hstable : (prefixWord ++ tailWord_4101777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101777).length < 2 ^ (prefixWord ++ tailWord_4101777).sum := by decide
  have hdescent : baseEnd_4101777 < baseStart_4101777 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101810 : List Nat := [3, 2, 1, 1, 1, 2, 3, 1, 1, 5, 3]
def baseStart_4101810 : Nat := 118140960795 + 4101810 * 2 ^ 59
def prefixEnd_4101810 : Nat := 4983230072969 + 3 ^ 40 * 4101810 * 2
def baseEnd_4101810 : Nat := 2106200083418701883211125

theorem tailTrace_4101810 : CollatzResearch.WordTrace tailWord_4101810 prefixEnd_4101810 2106200083418701883211125 := by
  unfold tailWord_4101810
  simp only [CollatzResearch.WordTrace]
  refine ⟨37401325317462594555199721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99736867513233585480532589 37401325317462594555199721)
  ·
    refine ⟨28050993988096945916399791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37401325317462594555199721 28050993988096945916399791)
    ·
      refine ⟨42076490982145418874599687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28050993988096945916399791 42076490982145418874599687)
      ·
        refine ⟨63114736473218128311899531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42076490982145418874599687 63114736473218128311899531)
        ·
          refine ⟨94672104709827192467849297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63114736473218128311899531 94672104709827192467849297)
          ·
            refine ⟨71004078532370394350886973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94672104709827192467849297 71004078532370394350886973)
            ·
              refine ⟨26626529449638897881582615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71004078532370394350886973 26626529449638897881582615)
              ·
                refine ⟨39939794174458346822373923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26626529449638897881582615 39939794174458346822373923)
                ·
                  refine ⟨59909691261687520233560885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39939794174458346822373923 59909691261687520233560885)
                  ·
                    refine ⟨5616533555783205021896333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59909691261687520233560885 5616533555783205021896333)
                    ·
                      refine ⟨2106200083418701883211125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5616533555783205021896333 2106200083418701883211125)
                      ·
                        rfl

theorem cell23_4101810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 1, 5, 3].length) (baseStart_4101810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4101810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4101810 prefixEnd_4101810 := by exact prefixLift 4101810
  have htrace : WordTrace (prefixWord ++ tailWord_4101810) baseStart_4101810 baseEnd_4101810 := by
    simpa [prefixWord, tailWord_4101810, baseEnd_4101810] using wordTrace_append hprefix tailTrace_4101810
  have hstable : (prefixWord ++ tailWord_4101810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101810).length < 2 ^ (prefixWord ++ tailWord_4101810).sum := by decide
  have hdescent : baseEnd_4101810 < baseStart_4101810 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101834 : List Nat := [3, 1, 2, 1, 5, 1, 2, 3, 5]
def baseStart_4101834 : Nat := 118140960795 + 4101834 * 2 ^ 59
def prefixEnd_4101834 : Nat := 4983230072969 + 3 ^ 40 * 4101834 * 2
def baseEnd_4101834 : Nat := 234023600772712198812335

theorem tailTrace_4101834 : CollatzResearch.WordTrace tailWord_4101834 prefixEnd_4101834 234023600772712198812335 := by
  unfold tailWord_4101834
  simp only [CollatzResearch.WordTrace]
  refine ⟨37401544155440857579918139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99737451081175620213115037 37401544155440857579918139)
  ·
    refine ⟨56102316233161286369877209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37401544155440857579918139 56102316233161286369877209)
    ·
      refine ⟨42076737174870964777407907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56102316233161286369877209 42076737174870964777407907)
      ·
        refine ⟨63115105762306447166111861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42076737174870964777407907 63115105762306447166111861)
        ·
          refine ⟨5917041165216229421822987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63115105762306447166111861 5917041165216229421822987)
          ·
            refine ⟨8875561747824344132734481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5917041165216229421822987 8875561747824344132734481)
            ·
              refine ⟨6656671310868258099550861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8875561747824344132734481 6656671310868258099550861)
              ·
                refine ⟨2496251741575596787331573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6656671310868258099550861 2496251741575596787331573)
                ·
                  refine ⟨234023600772712198812335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2496251741575596787331573 234023600772712198812335)
                  ·
                    rfl

theorem cell23_4101834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 3, 5].length) (baseStart_4101834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4101834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4101834 prefixEnd_4101834 := by exact prefixLift 4101834
  have htrace : WordTrace (prefixWord ++ tailWord_4101834) baseStart_4101834 baseEnd_4101834 := by
    simpa [prefixWord, tailWord_4101834, baseEnd_4101834] using wordTrace_append hprefix tailTrace_4101834
  have hstable : (prefixWord ++ tailWord_4101834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101834).length < 2 ^ (prefixWord ++ tailWord_4101834).sum := by decide
  have hdescent : baseEnd_4101834 < baseStart_4101834 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101867 : List Nat := [1, 1, 1, 1, 2, 4, 4, 1, 2, 4, 2]
def baseStart_4101867 : Nat := 118140960795 + 4101867 * 2 ^ 59
def prefixEnd_4101867 : Nat := 4983230072969 + 3 ^ 40 * 4101867 * 2
def baseEnd_4101867 : Nat := 2106229351816008160198363

theorem tailTrace_4101867 : CollatzResearch.WordTrace tailWord_4101867 prefixEnd_4101867 2106229351816008160198363 := by
  unfold tailWord_4101867
  simp only [CollatzResearch.WordTrace]
  refine ⟨149607380230643876955623855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99738253487095917970415903 149607380230643876955623855)
  ·
    refine ⟨224411070345965815433435783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149607380230643876955623855 224411070345965815433435783)
    ·
      refine ⟨336616605518948723150153675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224411070345965815433435783 336616605518948723150153675)
      ·
        refine ⟨504924908278423084725230513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336616605518948723150153675 504924908278423084725230513)
        ·
          refine ⟨378693681208817313543922885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 504924908278423084725230513 378693681208817313543922885)
          ·
            refine ⟨71005065226653246289485541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 378693681208817313543922885 71005065226653246289485541)
            ·
              refine ⟨13313449729997483679278539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71005065226653246289485541 13313449729997483679278539)
              ·
                refine ⟨19970174594996225518917809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13313449729997483679278539 19970174594996225518917809)
                ·
                  refine ⟨14977630946247169139188357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19970174594996225518917809 14977630946247169139188357)
                  ·
                    refine ⟨2808305802421344213597817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14977630946247169139188357 2808305802421344213597817)
                    ·
                      refine ⟨2106229351816008160198363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2808305802421344213597817 2106229351816008160198363)
                      ·
                        rfl

theorem cell23_4101867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 2, 4, 2].length) (baseStart_4101867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4101867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4101867 prefixEnd_4101867 := by exact prefixLift 4101867
  have htrace : WordTrace (prefixWord ++ tailWord_4101867) baseStart_4101867 baseEnd_4101867 := by
    simpa [prefixWord, tailWord_4101867, baseEnd_4101867] using wordTrace_append hprefix tailTrace_4101867
  have hstable : (prefixWord ++ tailWord_4101867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101867).length < 2 ^ (prefixWord ++ tailWord_4101867).sum := by decide
  have hdescent : baseEnd_4101867 < baseStart_4101867 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101924 : List Nat := [2, 3, 1, 3, 2, 1, 4, 1, 6]
def baseStart_4101924 : Nat := 118140960795 + 4101924 * 2 ^ 59
def prefixEnd_4101924 : Nat := 4983230072969 + 3 ^ 40 * 4101924 * 2
def baseEnd_4101924 : Nat := 234028735579257159687289

theorem tailTrace_4101924 : CollatzResearch.WordTrace tailWord_4101924 prefixEnd_4101924 234028735579257159687289 := by
  unfold tailWord_4101924
  simp only [CollatzResearch.WordTrace]
  refine ⟨74804729595718687845224413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99739639460958250460299217 74804729595718687845224413)
  ·
    refine ⟨28051773598394507941959155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74804729595718687845224413 28051773598394507941959155)
    ·
      refine ⟨42077660397591761912938733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28051773598394507941959155 42077660397591761912938733)
      ·
        refine ⟨15779122649096910717352025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42077660397591761912938733 15779122649096910717352025)
        ·
          refine ⟨11834341986822683038014019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15779122649096910717352025 11834341986822683038014019)
          ·
            refine ⟨17751512980234024557021029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11834341986822683038014019 17751512980234024557021029)
            ·
              refine ⟨3328408683793879604441443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17751512980234024557021029 3328408683793879604441443)
              ·
                refine ⟨4992613025690819406662165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3328408683793879604441443 4992613025690819406662165)
                ·
                  refine ⟨234028735579257159687289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4992613025690819406662165 234028735579257159687289)
                  ·
                    rfl

theorem cell23_4101924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 4, 1, 6].length) (baseStart_4101924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4101924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4101924 prefixEnd_4101924 := by exact prefixLift 4101924
  have htrace : WordTrace (prefixWord ++ tailWord_4101924) baseStart_4101924 baseEnd_4101924 := by
    simpa [prefixWord, tailWord_4101924, baseEnd_4101924] using wordTrace_append hprefix tailTrace_4101924
  have hstable : (prefixWord ++ tailWord_4101924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101924).length < 2 ^ (prefixWord ++ tailWord_4101924).sum := by decide
  have hdescent : baseEnd_4101924 < baseStart_4101924 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101937 : List Nat := [1, 2, 2, 3, 2, 3, 1, 1, 3, 5]
def baseStart_4101937 : Nat := 118140960795 + 4101937 * 2 ^ 59
def prefixEnd_4101937 : Nat := 4983230072969 + 3 ^ 40 * 4101937 * 2
def baseEnd_4101937 : Nat := 702088431820607628774347

theorem tailTrace_4101937 : CollatzResearch.WordTrace tailWord_4101937 prefixEnd_4101937 702088431820607628774347 := by
  unfold tailWord_4101937
  simp only [CollatzResearch.WordTrace]
  refine ⟨149609933340390278910672065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99739955560260185940448043 149609933340390278910672065)
  ·
    refine ⟨112207450005292709183004049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149609933340390278910672065 112207450005292709183004049)
    ·
      refine ⟨84155587503969531887253037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112207450005292709183004049 84155587503969531887253037)
      ·
        refine ⟨31558345313988574457719889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84155587503969531887253037 31558345313988574457719889)
        ·
          refine ⟨23668758985491430843289917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31558345313988574457719889 23668758985491430843289917)
          ·
            refine ⟨8875784619559286566233719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23668758985491430843289917 8875784619559286566233719)
            ·
              refine ⟨13313676929338929849350579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8875784619559286566233719 13313676929338929849350579)
              ·
                refine ⟨19970515394008394774025869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13313676929338929849350579 19970515394008394774025869)
                ·
                  refine ⟨7488943272753148040259701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19970515394008394774025869 7488943272753148040259701)
                  ·
                    refine ⟨702088431820607628774347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7488943272753148040259701 702088431820607628774347)
                    ·
                      rfl

theorem cell23_4101937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 3, 5].length) (baseStart_4101937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4101937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4101937 prefixEnd_4101937 := by exact prefixLift 4101937
  have htrace : WordTrace (prefixWord ++ tailWord_4101937) baseStart_4101937 baseEnd_4101937 := by
    simpa [prefixWord, tailWord_4101937, baseEnd_4101937] using wordTrace_append hprefix tailTrace_4101937
  have hstable : (prefixWord ++ tailWord_4101937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101937).length < 2 ^ (prefixWord ++ tailWord_4101937).sum := by decide
  have hdescent : baseEnd_4101937 < baseStart_4101937 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101944 : List Nat := [2, 1, 2, 1, 3, 3, 1, 3, 2, 3, 2]
def baseStart_4101944 : Nat := 118140960795 + 4101944 * 2 ^ 59
def prefixEnd_4101944 : Nat := 4983230072969 + 3 ^ 40 * 4101944 * 2
def baseEnd_4101944 : Nat := 2106268889826404358935509

theorem tailTrace_4101944 : CollatzResearch.WordTrace tailWord_4101944 prefixEnd_4101944 2106268889826404358935509 := by
  unfold tailWord_4101944
  simp only [CollatzResearch.WordTrace]
  refine ⟨74805094325682459553088443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99740125767576612737451257 74805094325682459553088443)
  ·
    refine ⟨112207641488523689329632665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74805094325682459553088443 112207641488523689329632665)
    ·
      refine ⟨84155731116392766997224499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112207641488523689329632665 84155731116392766997224499)
      ·
        refine ⟨126233596674589150495836749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84155731116392766997224499 126233596674589150495836749)
        ·
          refine ⟨47337598752970931435938781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126233596674589150495836749 47337598752970931435938781)
          ·
            refine ⟨17751599532364099288477043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47337598752970931435938781 17751599532364099288477043)
            ·
              refine ⟨26627399298546148932715565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17751599532364099288477043 26627399298546148932715565)
              ·
                refine ⟨9985274736954805849768337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26627399298546148932715565 9985274736954805849768337)
                ·
                  refine ⟨7488956052716104387326253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9985274736954805849768337 7488956052716104387326253)
                  ·
                    refine ⟨2808358519768539145247345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7488956052716104387326253 2808358519768539145247345)
                    ·
                      refine ⟨2106268889826404358935509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2808358519768539145247345 2106268889826404358935509)
                      ·
                        rfl

theorem cell23_4101944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 3, 2, 3, 2].length) (baseStart_4101944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4101944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4101944 prefixEnd_4101944 := by exact prefixLift 4101944
  have htrace : WordTrace (prefixWord ++ tailWord_4101944) baseStart_4101944 baseEnd_4101944 := by
    simpa [prefixWord, tailWord_4101944, baseEnd_4101944] using wordTrace_append hprefix tailTrace_4101944
  have hstable : (prefixWord ++ tailWord_4101944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101944).length < 2 ^ (prefixWord ++ tailWord_4101944).sum := by decide
  have hdescent : baseEnd_4101944 < baseStart_4101944 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101977 : List Nat := [1, 2, 1, 2, 2, 3, 1, 1, 5, 2, 3]
def baseStart_4101977 : Nat := 118140960795 + 4101977 * 2 ^ 59
def prefixEnd_4101977 : Nat := 4983230072969 + 3 ^ 40 * 4101977 * 2
def baseEnd_4101977 : Nat := 2106285834688002729822857

theorem tailTrace_4101977 : CollatzResearch.WordTrace tailWord_4101977 prefixEnd_4101977 2106285834688002729822857 := by
  unfold tailWord_4101977
  simp only [CollatzResearch.WordTrace]
  refine ⟨149611392260245365742128185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99740928173496910494752123 149611392260245365742128185)
  ·
    refine ⟨112208544195184024306596139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149611392260245365742128185 112208544195184024306596139)
    ·
      refine ⟨168312816292776036459894209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112208544195184024306596139 168312816292776036459894209)
      ·
        refine ⟨126234612219582027344920657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168312816292776036459894209 126234612219582027344920657)
        ·
          refine ⟨94675959164686520508690493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126234612219582027344920657 94675959164686520508690493)
          ·
            refine ⟨35503484686757445190758935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94675959164686520508690493 35503484686757445190758935)
            ·
              refine ⟨53255227030136167786138403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35503484686757445190758935 53255227030136167786138403)
              ·
                refine ⟨79882840545204251679207605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53255227030136167786138403 79882840545204251679207605)
                ·
                  refine ⟨7489016301112898594925713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79882840545204251679207605 7489016301112898594925713)
                  ·
                    refine ⟨5616762225834673946194285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7489016301112898594925713 5616762225834673946194285)
                    ·
                      refine ⟨2106285834688002729822857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5616762225834673946194285 2106285834688002729822857)
                      ·
                        rfl

theorem cell23_4101977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 5, 2, 3].length) (baseStart_4101977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4101977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4101977 prefixEnd_4101977 := by exact prefixLift 4101977
  have htrace : WordTrace (prefixWord ++ tailWord_4101977) baseStart_4101977 baseEnd_4101977 := by
    simpa [prefixWord, tailWord_4101977, baseEnd_4101977] using wordTrace_append hprefix tailTrace_4101977
  have hstable : (prefixWord ++ tailWord_4101977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101977).length < 2 ^ (prefixWord ++ tailWord_4101977).sum := by decide
  have hdescent : baseEnd_4101977 < baseStart_4101977 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101984 : List Nat := [2, 1, 1, 3, 3, 2, 2, 3, 2, 4]
def baseStart_4101984 : Nat := 118140960795 + 4101984 * 2 ^ 59
def prefixEnd_4101984 : Nat := 4983230072969 + 3 ^ 40 * 4101984 * 2
def baseEnd_4101984 : Nat := 702096476350861400811775

theorem tailTrace_4101984 : CollatzResearch.WordTrace tailWord_4101984 prefixEnd_4101984 702096476350861400811775 := by
  unfold tailWord_4101984
  simp only [CollatzResearch.WordTrace]
  refine ⟨74805823785610002968816503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99741098380813337291755337 74805823785610002968816503)
  ·
    refine ⟨112208735678415004453224755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74805823785610002968816503 112208735678415004453224755)
    ·
      refine ⟨168313103517622506679837133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112208735678415004453224755 168313103517622506679837133)
      ·
        refine ⟨63117413819108440004938925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168313103517622506679837133 63117413819108440004938925)
        ·
          refine ⟨23669030182165665001852097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63117413819108440004938925 23669030182165665001852097)
          ·
            refine ⟨17751772636624248751389073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23669030182165665001852097 17751772636624248751389073)
            ·
              refine ⟨13313829477468186563541805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17751772636624248751389073 13313829477468186563541805)
              ·
                refine ⟨4992686054050569961328177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13313829477468186563541805 4992686054050569961328177)
                ·
                  refine ⟨3744514540537927470996133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4992686054050569961328177 3744514540537927470996133)
                  ·
                    refine ⟨702096476350861400811775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3744514540537927470996133 702096476350861400811775)
                    ·
                      rfl

theorem cell23_4101984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 3, 2, 4].length) (baseStart_4101984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4101984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4101984 prefixEnd_4101984 := by exact prefixLift 4101984
  have htrace : WordTrace (prefixWord ++ tailWord_4101984) baseStart_4101984 baseEnd_4101984 := by
    simpa [prefixWord, tailWord_4101984, baseEnd_4101984] using wordTrace_append hprefix tailTrace_4101984
  have hstable : (prefixWord ++ tailWord_4101984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101984).length < 2 ^ (prefixWord ++ tailWord_4101984).sum := by decide
  have hdescent : baseEnd_4101984 < baseStart_4101984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101991 : List Nat := [1, 1, 5, 1, 2, 1, 3, 2, 3, 2, 2]
def baseStart_4101991 : Nat := 118140960795 + 4101991 * 2 ^ 59
def prefixEnd_4101991 : Nat := 4983230072969 + 3 ^ 40 * 4101991 * 2
def baseEnd_4101991 : Nat := 2106293023417165675047793

theorem tailTrace_4101991 : CollatzResearch.WordTrace tailWord_4101991 prefixEnd_4101991 2106293023417165675047793 := by
  unfold tailWord_4101991
  simp only [CollatzResearch.WordTrace]
  refine ⟨149611902882194646133137827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99741268588129764088758551 149611902882194646133137827)
  ·
    refine ⟨224417854323291969199706741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149611902882194646133137827 224417854323291969199706741)
    ·
      refine ⟨21039173842808622112472507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 224417854323291969199706741 21039173842808622112472507)
      ·
        refine ⟨31558760764212933168708761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21039173842808622112472507 31558760764212933168708761)
        ·
          refine ⟨23669070573159699876531571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31558760764212933168708761 23669070573159699876531571)
          ·
            refine ⟨35503605859739549814797357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23669070573159699876531571 35503605859739549814797357)
            ·
              refine ⟨13313852197402331180549009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35503605859739549814797357 13313852197402331180549009)
              ·
                refine ⟨9985389148051748385411757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13313852197402331180549009 9985389148051748385411757)
                ·
                  refine ⟨3744520930519405644529409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9985389148051748385411757 3744520930519405644529409)
                  ·
                    refine ⟨2808390697889554233397057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3744520930519405644529409 2808390697889554233397057)
                    ·
                      refine ⟨2106293023417165675047793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2808390697889554233397057 2106293023417165675047793)
                      ·
                        rfl

theorem cell23_4101991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 2, 3, 2, 2].length) (baseStart_4101991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4101991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4101991 prefixEnd_4101991 := by exact prefixLift 4101991
  have htrace : WordTrace (prefixWord ++ tailWord_4101991) baseStart_4101991 baseEnd_4101991 := by
    simpa [prefixWord, tailWord_4101991, baseEnd_4101991] using wordTrace_append hprefix tailTrace_4101991
  have hstable : (prefixWord ++ tailWord_4101991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101991).length < 2 ^ (prefixWord ++ tailWord_4101991).sum := by decide
  have hdescent : baseEnd_4101991 < baseStart_4101991 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102014 : List Nat := [4, 2, 3, 1, 1, 2, 10]
def baseStart_4102014 : Nat := 118140960795 + 4102014 * 2 ^ 59
def prefixEnd_4102014 : Nat := 4983230072969 + 3 ^ 40 * 4102014 * 2
def baseEnd_4102014 : Nat := 26003763376200235618027

theorem tailTrace_4102014 : CollatzResearch.WordTrace tailWord_4102014 prefixEnd_4102014 26003763376200235618027 := by
  unfold tailWord_4102014
  simp only [CollatzResearch.WordTrace]
  refine ⟨18701592720138915132653137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99741827840740880707483397 18701592720138915132653137)
  ·
    refine ⟨14026194540104186349489853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18701592720138915132653137 14026194540104186349489853)
    ·
      refine ⟨5259822952539069881058695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14026194540104186349489853 5259822952539069881058695)
      ·
        refine ⟨7889734428808604821588043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5259822952539069881058695 7889734428808604821588043)
        ·
          refine ⟨11834601643212907232382065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7889734428808604821588043 11834601643212907232382065)
          ·
            refine ⟨8875951232409680424286549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11834601643212907232382065 8875951232409680424286549)
            ·
              refine ⟨26003763376200235618027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8875951232409680424286549 26003763376200235618027)
              ·
                rfl

theorem cell23_4102014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 10].length) (baseStart_4102014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4102014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4102014 prefixEnd_4102014 := by exact prefixLift 4102014
  have htrace : WordTrace (prefixWord ++ tailWord_4102014) baseStart_4102014 baseEnd_4102014 := by
    simpa [prefixWord, tailWord_4102014, baseEnd_4102014] using wordTrace_append hprefix tailTrace_4102014
  have hstable : (prefixWord ++ tailWord_4102014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102014).length < 2 ^ (prefixWord ++ tailWord_4102014).sum := by decide
  have hdescent : baseEnd_4102014 < baseStart_4102014 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102038 : List Nat := [5, 3, 1, 1, 2, 1, 1, 1, 1, 1, 6]
def baseStart_4102038 : Nat := 118140960795 + 4102038 * 2 ^ 59
def prefixEnd_4102038 : Nat := 4983230072969 + 3 ^ 40 * 4102038 * 2
def baseEnd_4102038 : Nat := 2106317157007926991160077

theorem tailTrace_4102038 : CollatzResearch.WordTrace tailWord_4102038 prefixEnd_4102038 2106317157007926991160077 := by
  unfold tailWord_4102038
  simp only [CollatzResearch.WordTrace]
  refine ⟨9350851069564023322506173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99742411408682915440065845 9350851069564023322506173)
  ·
    refine ⟨3506569151086508745939815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9350851069564023322506173 3506569151086508745939815)
    ·
      refine ⟨5259853726629763118909723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3506569151086508745939815 5259853726629763118909723)
      ·
        refine ⟨7889780589944644678364585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5259853726629763118909723 7889780589944644678364585)
        ·
          refine ⟨5917335442458483508773439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7889780589944644678364585 5917335442458483508773439)
          ·
            refine ⟨8876003163687725263160159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5917335442458483508773439 8876003163687725263160159)
            ·
              refine ⟨13314004745531587894740239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8876003163687725263160159 13314004745531587894740239)
              ·
                refine ⟨19971007118297381842110359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13314004745531587894740239 19971007118297381842110359)
                ·
                  refine ⟨29956510677446072763165539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19971007118297381842110359 29956510677446072763165539)
                  ·
                    refine ⟨44934766016169109144748309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29956510677446072763165539 44934766016169109144748309)
                    ·
                      refine ⟨2106317157007926991160077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44934766016169109144748309 2106317157007926991160077)
                      ·
                        rfl

theorem cell23_4102038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_4102038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4102038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4102038 prefixEnd_4102038 := by exact prefixLift 4102038
  have htrace : WordTrace (prefixWord ++ tailWord_4102038) baseStart_4102038 baseEnd_4102038 := by
    simpa [prefixWord, tailWord_4102038, baseEnd_4102038] using wordTrace_append hprefix tailTrace_4102038
  have hstable : (prefixWord ++ tailWord_4102038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102038).length < 2 ^ (prefixWord ++ tailWord_4102038).sum := by decide
  have hdescent : baseEnd_4102038 < baseStart_4102038 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102067 : List Nat := [1, 1, 1, 2, 3, 1, 5, 1, 2, 1, 5]
def baseStart_4102067 : Nat := 118140960795 + 4102067 * 2 ^ 59
def prefixEnd_4102067 : Nat := 4983230072969 + 3 ^ 40 * 4102067 * 2
def baseEnd_4102067 : Nat := 2106332047946907377697443

theorem tailTrace_4102067 : CollatzResearch.WordTrace tailWord_4102067 prefixEnd_4102067 2106332047946907377697443 := by
  unfold tailWord_4102067
  simp only [CollatzResearch.WordTrace]
  refine ⟨149614674829919311112904455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99743116553279540741936303 149614674829919311112904455)
  ·
    refine ⟨224422012244878966669356683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149614674829919311112904455 224422012244878966669356683)
    ·
      refine ⟨336633018367318450004035025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224422012244878966669356683 336633018367318450004035025)
      ·
        refine ⟨252474763775488837503026269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336633018367318450004035025 252474763775488837503026269)
        ·
          refine ⟨94678036415808314063634851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252474763775488837503026269 94678036415808314063634851)
          ·
            refine ⟨142017054623712471095452277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94678036415808314063634851 142017054623712471095452277)
            ·
              refine ⟨13314098870973044165198651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 142017054623712471095452277 13314098870973044165198651)
              ·
                refine ⟨19971148306459566247797977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13314098870973044165198651 19971148306459566247797977)
                ·
                  refine ⟨14978361229844674685848483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19971148306459566247797977 14978361229844674685848483)
                  ·
                    refine ⟨22467541844767012028772725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14978361229844674685848483 22467541844767012028772725)
                    ·
                      refine ⟨2106332047946907377697443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22467541844767012028772725 2106332047946907377697443)
                      ·
                        rfl

theorem cell23_4102067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 2, 1, 5].length) (baseStart_4102067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4102067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4102067 prefixEnd_4102067 := by exact prefixLift 4102067
  have htrace : WordTrace (prefixWord ++ tailWord_4102067) baseStart_4102067 baseEnd_4102067 := by
    simpa [prefixWord, tailWord_4102067, baseEnd_4102067] using wordTrace_append hprefix tailTrace_4102067
  have hstable : (prefixWord ++ tailWord_4102067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102067).length < 2 ^ (prefixWord ++ tailWord_4102067).sum := by decide
  have hdescent : baseEnd_4102067 < baseStart_4102067 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102102 : List Nat := [5, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2]
def baseStart_4102102 : Nat := 118140960795 + 4102102 * 2 ^ 59
def prefixEnd_4102102 : Nat := 4983230072969 + 3 ^ 40 * 4102102 * 2
def baseEnd_4102102 : Nat := 2106350019769814740759783

theorem tailTrace_4102102 : CollatzResearch.WordTrace tailWord_4102102 prefixEnd_4102102 2106350019769814740759783 := by
  unfold tailWord_4102102
  simp only [CollatzResearch.WordTrace]
  refine ⟨9350996961549532005651785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99743967589861674726952373 9350996961549532005651785)
  ·
    refine ⟨7013247721162149004238839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9350996961549532005651785 7013247721162149004238839)
    ·
      refine ⟨10519871581743223506358259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7013247721162149004238839 10519871581743223506358259)
      ·
        refine ⟨15779807372614835259537389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10519871581743223506358259 15779807372614835259537389)
        ·
          refine ⟨5917427764730563222326521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15779807372614835259537389 5917427764730563222326521)
          ·
            refine ⟨4438070823547922416744891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5917427764730563222326521 4438070823547922416744891)
            ·
              refine ⟨6657106235321883625117337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4438070823547922416744891 6657106235321883625117337)
              ·
                refine ⟨4992829676491412718838003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6657106235321883625117337 4992829676491412718838003)
                ·
                  refine ⟨7489244514737119078257005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4992829676491412718838003 7489244514737119078257005)
                  ·
                    refine ⟨2808466693026419654346377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7489244514737119078257005 2808466693026419654346377)
                    ·
                      refine ⟨2106350019769814740759783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2808466693026419654346377 2106350019769814740759783)
                      ·
                        rfl

theorem cell23_4102102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2].length) (baseStart_4102102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4102102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4102102 prefixEnd_4102102 := by exact prefixLift 4102102
  have htrace : WordTrace (prefixWord ++ tailWord_4102102) baseStart_4102102 baseEnd_4102102 := by
    simpa [prefixWord, tailWord_4102102, baseEnd_4102102] using wordTrace_append hprefix tailTrace_4102102
  have hstable : (prefixWord ++ tailWord_4102102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102102).length < 2 ^ (prefixWord ++ tailWord_4102102).sum := by decide
  have hdescent : baseEnd_4102102 < baseStart_4102102 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102124 : List Nat := [2, 2, 1, 1, 2, 1, 1, 2, 4, 5, 2]
def baseStart_4102124 : Nat := 118140960795 + 4102124 * 2 ^ 59
def prefixEnd_4102124 : Nat := 4983230072969 + 3 ^ 40 * 4102124 * 2
def baseEnd_4102124 : Nat := 2106361316344213654684681

theorem tailTrace_4102124 : CollatzResearch.WordTrace tailWord_4102124 prefixEnd_4102124 2106361316344213654684681 := by
  unfold tailWord_4102124
  simp only [CollatzResearch.WordTrace]
  refine ⟨74808376895356404923864713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99744502527141873231819617 74808376895356404923864713)
  ·
    refine ⟨56106282671517303692898535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74808376895356404923864713 56106282671517303692898535)
    ·
      refine ⟨84159424007275955539347803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56106282671517303692898535 84159424007275955539347803)
      ·
        refine ⟨126239136010913933309021705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84159424007275955539347803 126239136010913933309021705)
        ·
          refine ⟨94679352008185449981766279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126239136010913933309021705 94679352008185449981766279)
          ·
            refine ⟨142019028012278174972649419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94679352008185449981766279 142019028012278174972649419)
            ·
              refine ⟨213028542018417262458974129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142019028012278174972649419 213028542018417262458974129)
              ·
                refine ⟨159771406513812946844230597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213028542018417262458974129 159771406513812946844230597)
                ·
                  refine ⟨29957138721339927533293237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 159771406513812946844230597 29957138721339927533293237)
                  ·
                    refine ⟨2808481755125618206246241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29957138721339927533293237 2808481755125618206246241)
                    ·
                      refine ⟨2106361316344213654684681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2808481755125618206246241 2106361316344213654684681)
                      ·
                        rfl

theorem cell23_4102124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 5, 2].length) (baseStart_4102124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4102124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4102124 prefixEnd_4102124 := by exact prefixLift 4102124
  have htrace : WordTrace (prefixWord ++ tailWord_4102124) baseStart_4102124 baseEnd_4102124 := by
    simpa [prefixWord, tailWord_4102124, baseEnd_4102124] using wordTrace_append hprefix tailTrace_4102124
  have hstable : (prefixWord ++ tailWord_4102124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102124).length < 2 ^ (prefixWord ++ tailWord_4102124).sum := by decide
  have hdescent : baseEnd_4102124 < baseStart_4102124 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102127 : List Nat := [1, 1, 2, 1, 4, 2, 1, 1, 3, 2, 5]
def baseStart_4102127 : Nat := 118140960795 + 4102127 * 2 ^ 59
def prefixEnd_4102127 : Nat := 4983230072969 + 3 ^ 40 * 4102127 * 2
def baseEnd_4102127 : Nat := 2106362856786177142947167

theorem tailTrace_4102127 : CollatzResearch.WordTrace tailWord_4102127 prefixEnd_4102127 2106362856786177142947167 := by
  unfold tailWord_4102127
  simp only [CollatzResearch.WordTrace]
  refine ⟨149616863209701941360088635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99744575473134627573392423 149616863209701941360088635)
  ·
    refine ⟨224425294814552912040132953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149616863209701941360088635 224425294814552912040132953)
    ·
      refine ⟨168318971110914684030099715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224425294814552912040132953 168318971110914684030099715)
      ·
        refine ⟨252478456666372026045149573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168318971110914684030099715 252478456666372026045149573)
        ·
          refine ⟨47339710624944754883465545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 252478456666372026045149573 47339710624944754883465545)
          ·
            refine ⟨35504782968708566162599159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47339710624944754883465545 35504782968708566162599159)
            ·
              refine ⟨53257174453062849243898739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35504782968708566162599159 53257174453062849243898739)
              ·
                refine ⟨79885761679594273865848109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53257174453062849243898739 79885761679594273865848109)
                ·
                  refine ⟨29957160629847852699693041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79885761679594273865848109 29957160629847852699693041)
                  ·
                    refine ⟨22467870472385889524769781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29957160629847852699693041 22467870472385889524769781)
                    ·
                      refine ⟨2106362856786177142947167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22467870472385889524769781 2106362856786177142947167)
                      ·
                        rfl

theorem cell23_4102127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 2, 5].length) (baseStart_4102127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4102127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4102127 prefixEnd_4102127 := by exact prefixLift 4102127
  have htrace : WordTrace (prefixWord ++ tailWord_4102127) baseStart_4102127 baseEnd_4102127 := by
    simpa [prefixWord, tailWord_4102127, baseEnd_4102127] using wordTrace_append hprefix tailTrace_4102127
  have hstable : (prefixWord ++ tailWord_4102127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102127).length < 2 ^ (prefixWord ++ tailWord_4102127).sum := by decide
  have hdescent : baseEnd_4102127 < baseStart_4102127 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102148 : List Nat := [2, 3, 2, 4, 1, 1, 1, 1, 2, 3, 3]
def baseStart_4102148 : Nat := 118140960795 + 4102148 * 2 ^ 59
def prefixEnd_4102148 : Nat := 4983230072969 + 3 ^ 40 * 4102148 * 2
def baseEnd_4102148 : Nat := 2106373639879921560784571

theorem tailTrace_4102148 : CollatzResearch.WordTrace tailWord_4102148 prefixEnd_4102148 2106373639879921560784571 := by
  unfold tailWord_4102148
  simp only [CollatzResearch.WordTrace]
  refine ⟨74808814571312930973301549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99745086095083907964402065 74808814571312930973301549)
  ·
    refine ⟨28053305464242349114988081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74808814571312930973301549 28053305464242349114988081)
    ·
      refine ⟨21039979098181761836241061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28053305464242349114988081 21039979098181761836241061)
      ·
        refine ⟨3944996080909080344295199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21039979098181761836241061 3944996080909080344295199)
        ·
          refine ⟨5917494121363620516442799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3944996080909080344295199 5917494121363620516442799)
          ·
            refine ⟨8876241182045430774664199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5917494121363620516442799 8876241182045430774664199)
            ·
              refine ⟨13314361773068146161996299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8876241182045430774664199 13314361773068146161996299)
              ·
                refine ⟨19971542659602219242994449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13314361773068146161996299 19971542659602219242994449)
                ·
                  refine ⟨14978656994701664432245837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19971542659602219242994449 14978656994701664432245837)
                  ·
                    refine ⟨5616996373013124162092189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14978656994701664432245837 5616996373013124162092189)
                    ·
                      refine ⟨2106373639879921560784571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5616996373013124162092189 2106373639879921560784571)
                      ·
                        rfl

theorem cell23_4102148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_4102148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4102148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4102148 prefixEnd_4102148 := by exact prefixLift 4102148
  have htrace : WordTrace (prefixWord ++ tailWord_4102148) baseStart_4102148 baseEnd_4102148 := by
    simpa [prefixWord, tailWord_4102148, baseEnd_4102148] using wordTrace_append hprefix tailTrace_4102148
  have hstable : (prefixWord ++ tailWord_4102148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102148).length < 2 ^ (prefixWord ++ tailWord_4102148).sum := by decide
  have hdescent : baseEnd_4102148 < baseStart_4102148 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102194 : List Nat := [3, 2, 1, 1, 2, 4, 1, 1, 8]
def baseStart_4102194 : Nat := 118140960795 + 4102194 * 2 ^ 59
def prefixEnd_4102194 : Nat := 4983230072969 + 3 ^ 40 * 4102194 * 2
def baseEnd_4102194 : Nat := 234044139998892042312151

theorem tailTrace_4102194 : CollatzResearch.WordTrace tailWord_4102194 prefixEnd_4102194 234044139998892042312151 := by
  unfold tailWord_4102194
  simp only [CollatzResearch.WordTrace]
  refine ⟨37404826725114802950694409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99746204600306141201851757 37404826725114802950694409)
  ·
    refine ⟨28053620043836102213020807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37404826725114802950694409 28053620043836102213020807)
    ·
      refine ⟨42080430065754153319531211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28053620043836102213020807 42080430065754153319531211)
      ·
        refine ⟨63120645098631229979296817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42080430065754153319531211 63120645098631229979296817)
        ·
          refine ⟨47340483823973422484472613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63120645098631229979296817 47340483823973422484472613)
          ·
            refine ⟨8876340716995016715838615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47340483823973422484472613 8876340716995016715838615)
            ·
              refine ⟨13314511075492525073757923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8876340716995016715838615 13314511075492525073757923)
              ·
                refine ⟨19971766613238787610636885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13314511075492525073757923 19971766613238787610636885)
                ·
                  refine ⟨234044139998892042312151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19971766613238787610636885 234044139998892042312151)
                  ·
                    rfl

theorem cell23_4102194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 8].length) (baseStart_4102194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4102194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4102194 prefixEnd_4102194 := by exact prefixLift 4102194
  have htrace : WordTrace (prefixWord ++ tailWord_4102194) baseStart_4102194 baseEnd_4102194 := by
    simpa [prefixWord, tailWord_4102194, baseEnd_4102194] using wordTrace_append hprefix tailTrace_4102194
  have hstable : (prefixWord ++ tailWord_4102194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102194).length < 2 ^ (prefixWord ++ tailWord_4102194).sum := by decide
  have hdescent : baseEnd_4102194 < baseStart_4102194 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102198 : List Nat := [5, 1, 2, 1, 1, 1, 4, 1, 3, 4]
def baseStart_4102198 : Nat := 118140960795 + 4102198 * 2 ^ 59
def prefixEnd_4102198 : Nat := 4983230072969 + 3 ^ 40 * 4102198 * 2
def baseEnd_4102198 : Nat := 702133104637548788386447

theorem tailTrace_4102198 : CollatzResearch.WordTrace tailWord_4102198 prefixEnd_4102198 702133104637548788386447 := by
  unfold tailWord_4102198
  simp only [CollatzResearch.WordTrace]
  refine ⟨9351215799527795030370203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99746301861629813657282165 9351215799527795030370203)
  ·
    refine ⟨14026823699291692545555305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9351215799527795030370203 14026823699291692545555305)
    ·
      refine ⟨10520117774468769409166479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14026823699291692545555305 10520117774468769409166479)
      ·
        refine ⟨15780176661703154113749719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10520117774468769409166479 15780176661703154113749719)
        ·
          refine ⟨23670264992554731170624579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15780176661703154113749719 23670264992554731170624579)
          ·
            refine ⟨35505397488832096755936869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23670264992554731170624579 35505397488832096755936869)
            ·
              refine ⟨6657262029156018141738163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35505397488832096755936869 6657262029156018141738163)
              ·
                refine ⟨9985893043734027212607245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6657262029156018141738163 9985893043734027212607245)
                ·
                  refine ⟨3744709891400260204727717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9985893043734027212607245 3744709891400260204727717)
                  ·
                    refine ⟨702133104637548788386447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3744709891400260204727717 702133104637548788386447)
                    ·
                      rfl

theorem cell23_4102198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_4102198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4102198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4102198 prefixEnd_4102198 := by exact prefixLift 4102198
  have htrace : WordTrace (prefixWord ++ tailWord_4102198) baseStart_4102198 baseEnd_4102198 := by
    simpa [prefixWord, tailWord_4102198, baseEnd_4102198] using wordTrace_append hprefix tailTrace_4102198
  have hstable : (prefixWord ++ tailWord_4102198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102198).length < 2 ^ (prefixWord ++ tailWord_4102198).sum := by decide
  have hdescent : baseEnd_4102198 < baseStart_4102198 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102221 : List Nat := [1, 6, 1, 1, 1, 1, 1, 1, 2, 5, 3]
def baseStart_4102221 : Nat := 118140960795 + 4102221 * 2 ^ 59
def prefixEnd_4102221 : Nat := 4983230072969 + 3 ^ 40 * 4102221 * 2
def baseEnd_4102221 : Nat := 2106411123967699775171735

theorem tailTrace_4102221 : CollatzResearch.WordTrace tailWord_4102221 prefixEnd_4102221 2106411123967699775171735 := by
  unfold tailWord_4102221
  simp only [CollatzResearch.WordTrace]
  refine ⟨149620291671361395414010517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99746861114240930276007011 149620291671361395414010517)
  ·
    refine ⟨7013451172095065410031743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 149620291671361395414010517 7013451172095065410031743)
    ·
      refine ⟨10520176758142598115047615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7013451172095065410031743 10520176758142598115047615)
      ·
        refine ⟨15780265137213897172571423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10520176758142598115047615 15780265137213897172571423)
        ·
          refine ⟨23670397705820845758857135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15780265137213897172571423 23670397705820845758857135)
          ·
            refine ⟨35505596558731268638285703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23670397705820845758857135 35505596558731268638285703)
            ·
              refine ⟨53258394838096902957428555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35505596558731268638285703 53258394838096902957428555)
              ·
                refine ⟨79887592257145354436142833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53258394838096902957428555 79887592257145354436142833)
                ·
                  refine ⟨59915694192859015827107125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79887592257145354436142833 59915694192859015827107125)
                  ·
                    refine ⟨5617096330580532733791293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59915694192859015827107125 5617096330580532733791293)
                    ·
                      refine ⟨2106411123967699775171735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5617096330580532733791293 2106411123967699775171735)
                      ·
                        rfl

theorem cell23_4102221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_4102221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4102221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4102221 prefixEnd_4102221 := by exact prefixLift 4102221
  have htrace : WordTrace (prefixWord ++ tailWord_4102221) baseStart_4102221 baseEnd_4102221 := by
    simpa [prefixWord, tailWord_4102221, baseEnd_4102221] using wordTrace_append hprefix tailTrace_4102221
  have hstable : (prefixWord ++ tailWord_4102221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102221).length < 2 ^ (prefixWord ++ tailWord_4102221).sum := by decide
  have hdescent : baseEnd_4102221 < baseStart_4102221 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102231 : List Nat := [1, 1, 3, 2, 2, 1, 4, 1, 1, 5, 2]
def baseStart_4102231 : Nat := 118140960795 + 4102231 * 2 ^ 59
def prefixEnd_4102231 : Nat := 4983230072969 + 3 ^ 40 * 4102231 * 2
def baseEnd_4102231 : Nat := 2106416258774244736046689

theorem tailTrace_4102231 : CollatzResearch.WordTrace tailWord_4102231 prefixEnd_4102231 2106416258774244736046689 := by
  unfold tailWord_4102231
  simp only [CollatzResearch.WordTrace]
  refine ⟨149620656401325167121874547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99747104267550111414583031 149620656401325167121874547)
  ·
    refine ⟨224430984601987750682811821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149620656401325167121874547 224430984601987750682811821)
    ·
      refine ⟨84161619225745406506054433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224430984601987750682811821 84161619225745406506054433)
      ·
        refine ⟨63121214419309054879540825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84161619225745406506054433 63121214419309054879540825)
        ·
          refine ⟨47340910814481791159655619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63121214419309054879540825 47340910814481791159655619)
          ·
            refine ⟨71011366221722686739483429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47340910814481791159655619 71011366221722686739483429)
            ·
              refine ⟨13314631166573003763653143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71011366221722686739483429 13314631166573003763653143)
              ·
                refine ⟨19971946749859505645479715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13314631166573003763653143 19971946749859505645479715)
                ·
                  refine ⟨29957920124789258468219573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19971946749859505645479715 29957920124789258468219573)
                  ·
                    refine ⟨2808555011698992981395585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29957920124789258468219573 2808555011698992981395585)
                    ·
                      refine ⟨2106416258774244736046689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2808555011698992981395585 2106416258774244736046689)
                      ·
                        rfl

theorem cell23_4102231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 5, 2].length) (baseStart_4102231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4102231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4102231 prefixEnd_4102231 := by exact prefixLift 4102231
  have htrace : WordTrace (prefixWord ++ tailWord_4102231) baseStart_4102231 baseEnd_4102231 := by
    simpa [prefixWord, tailWord_4102231, baseEnd_4102231] using wordTrace_append hprefix tailTrace_4102231
  have hstable : (prefixWord ++ tailWord_4102231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102231).length < 2 ^ (prefixWord ++ tailWord_4102231).sum := by decide
  have hdescent : baseEnd_4102231 < baseStart_4102231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102264 : List Nat := [2, 1, 2, 1, 1, 1, 3, 1, 2, 6, 3]
def baseStart_4102264 : Nat := 118140960795 + 4102264 * 2 ^ 59
def prefixEnd_4102264 : Nat := 4983230072969 + 3 ^ 40 * 4102264 * 2
def baseEnd_4102264 : Nat := 2106433203635843106934037

theorem tailTrace_4102264 : CollatzResearch.WordTrace tailWord_4102264 prefixEnd_4102264 2106433203635843106934037 := by
  unfold tailWord_4102264
  simp only [CollatzResearch.WordTrace]
  refine ⟨74810930005102806878912923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99747906673470409171883897 74810930005102806878912923)
  ·
    refine ⟨112216395007654210318369385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74810930005102806878912923 112216395007654210318369385)
    ·
      refine ⟨84162296255740657738777039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112216395007654210318369385 84162296255740657738777039)
      ·
        refine ⟨126243444383610986608165559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84162296255740657738777039 126243444383610986608165559)
        ·
          refine ⟨189365166575416479912248339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126243444383610986608165559 189365166575416479912248339)
          ·
            refine ⟨284047749863124719868372509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189365166575416479912248339 284047749863124719868372509)
            ·
              refine ⟨106517906198671769950639691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 284047749863124719868372509 106517906198671769950639691)
              ·
                refine ⟨159776859298007654925959537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106517906198671769950639691 159776859298007654925959537)
                ·
                  refine ⟨119832644473505741194469653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159776859298007654925959537 119832644473505741194469653)
                  ·
                    refine ⟨5617155209695581618490765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 119832644473505741194469653 5617155209695581618490765)
                    ·
                      refine ⟨2106433203635843106934037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5617155209695581618490765 2106433203635843106934037)
                      ·
                        rfl

theorem cell23_4102264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 2, 6, 3].length) (baseStart_4102264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4102264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4102264 prefixEnd_4102264 := by exact prefixLift 4102264
  have htrace : WordTrace (prefixWord ++ tailWord_4102264) baseStart_4102264 baseEnd_4102264 := by
    simpa [prefixWord, tailWord_4102264, baseEnd_4102264] using wordTrace_append hprefix tailTrace_4102264
  have hstable : (prefixWord ++ tailWord_4102264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102264).length < 2 ^ (prefixWord ++ tailWord_4102264).sum := by decide
  have hdescent : baseEnd_4102264 < baseStart_4102264 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102281 : List Nat := [1, 2, 1, 1, 4, 2, 3, 1, 3, 2, 3]
def baseStart_4102281 : Nat := 118140960795 + 4102281 * 2 ^ 59
def prefixEnd_4102281 : Nat := 4983230072969 + 3 ^ 40 * 4102281 * 2
def baseEnd_4102281 : Nat := 2106441932806969540421459

theorem tailTrace_4102281 : CollatzResearch.WordTrace tailWord_4102281 prefixEnd_4102281 2106441932806969540421459 := by
  unfold tailWord_4102281
  simp only [CollatzResearch.WordTrace]
  refine ⟨149622480051144025661194697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99748320034096017107463131 149622480051144025661194697)
  ·
    refine ⟨112216860038358019245896023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149622480051144025661194697 112216860038358019245896023)
    ·
      refine ⟨168325290057537028868844035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112216860038358019245896023 168325290057537028868844035)
      ·
        refine ⟨252487935086305543303266053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168325290057537028868844035 252487935086305543303266053)
        ·
          refine ⟨47341487828682289369362385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 252487935086305543303266053 47341487828682289369362385)
          ·
            refine ⟨35506115871511717027021789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47341487828682289369362385 35506115871511717027021789)
            ·
              refine ⟨13314793451816893885133171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35506115871511717027021789 13314793451816893885133171)
              ·
                refine ⟨19972190177725340827699757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13314793451816893885133171 19972190177725340827699757)
                ·
                  refine ⟨7489571316647002810387409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19972190177725340827699757 7489571316647002810387409)
                  ·
                    refine ⟨5617178487485252107790557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7489571316647002810387409 5617178487485252107790557)
                    ·
                      refine ⟨2106441932806969540421459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5617178487485252107790557 2106441932806969540421459)
                      ·
                        rfl

theorem cell23_4102281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 3, 2, 3].length) (baseStart_4102281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4102281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4102281 prefixEnd_4102281 := by exact prefixLift 4102281
  have htrace : WordTrace (prefixWord ++ tailWord_4102281) baseStart_4102281 baseEnd_4102281 := by
    simpa [prefixWord, tailWord_4102281, baseEnd_4102281] using wordTrace_append hprefix tailTrace_4102281
  have hstable : (prefixWord ++ tailWord_4102281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102281).length < 2 ^ (prefixWord ++ tailWord_4102281).sum := by decide
  have hdescent : baseEnd_4102281 < baseStart_4102281 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102292 : List Nat := [2, 4, 2, 3, 1, 1, 3, 1, 1, 5]
def baseStart_4102292 : Nat := 118140960795 + 4102292 * 2 ^ 59
def prefixEnd_4102292 : Nat := 4983230072969 + 3 ^ 40 * 4102292 * 2
def baseEnd_4102292 : Nat := 702149193698056332461303

theorem tailTrace_4102292 : CollatzResearch.WordTrace tailWord_4102292 prefixEnd_4102292 702149193698056332461303 := by
  unfold tailWord_4102292
  simp only [CollatzResearch.WordTrace]
  refine ⟨74811440627052087269922565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99748587502736116359896753 74811440627052087269922565)
  ·
    refine ⟨14027145117572266363110481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74811440627052087269922565 14027145117572266363110481)
    ·
      refine ⟨10520358838179199772332861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14027145117572266363110481 10520358838179199772332861)
      ·
        refine ⟨3945134564317199914624823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10520358838179199772332861 3945134564317199914624823)
        ·
          refine ⟨5917701846475799871937235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3945134564317199914624823 5917701846475799871937235)
          ·
            refine ⟨8876552769713699807905853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5917701846475799871937235 8876552769713699807905853)
            ·
              refine ⟨3328707288642637427964695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8876552769713699807905853 3328707288642637427964695)
              ·
                refine ⟨4993060932963956141947043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3328707288642637427964695 4993060932963956141947043)
                ·
                  refine ⟨7489591399445934212920565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4993060932963956141947043 7489591399445934212920565)
                  ·
                    refine ⟨702149193698056332461303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7489591399445934212920565 702149193698056332461303)
                    ·
                      rfl

theorem cell23_4102292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_4102292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4102292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4102292 prefixEnd_4102292 := by exact prefixLift 4102292
  have htrace : WordTrace (prefixWord ++ tailWord_4102292) baseStart_4102292 baseEnd_4102292 := by
    simpa [prefixWord, tailWord_4102292, baseEnd_4102292] using wordTrace_append hprefix tailTrace_4102292
  have hstable : (prefixWord ++ tailWord_4102292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102292).length < 2 ^ (prefixWord ++ tailWord_4102292).sum := by decide
  have hdescent : baseEnd_4102292 < baseStart_4102292 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102295 : List Nat := [1, 1, 3, 3, 4, 1, 3, 1, 1, 1, 4]
def baseStart_4102295 : Nat := 118140960795 + 4102295 * 2 ^ 59
def prefixEnd_4102295 : Nat := 4983230072969 + 3 ^ 40 * 4102295 * 2
def baseEnd_4102295 : Nat := 2106449121536132485646395

theorem tailTrace_4102295 : CollatzResearch.WordTrace tailWord_4102295 prefixEnd_4102295 2106449121536132485646395 := by
  unfold tailWord_4102295
  simp only [CollatzResearch.WordTrace]
  refine ⟨149622990673093306052204339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99748660448728870701469559 149622990673093306052204339)
  ·
    refine ⟨224434486009639959078306509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149622990673093306052204339 224434486009639959078306509)
    ·
      refine ⟨84162932253614984654364941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224434486009639959078306509 84162932253614984654364941)
      ·
        refine ⟨31561099595105619245386853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84162932253614984654364941 31561099595105619245386853)
        ·
          refine ⟨5917706174082303608510035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31561099595105619245386853 5917706174082303608510035)
          ·
            refine ⟨8876559261123455412765053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5917706174082303608510035 8876559261123455412765053)
            ·
              refine ⟨3328709722921295779786895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8876559261123455412765053 3328709722921295779786895)
              ·
                refine ⟨4993064584381943669680343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3328709722921295779786895 4993064584381943669680343)
                ·
                  refine ⟨7489596876572915504520515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4993064584381943669680343 7489596876572915504520515)
                  ·
                    refine ⟨11234395314859373256780773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7489596876572915504520515 11234395314859373256780773)
                    ·
                      refine ⟨2106449121536132485646395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11234395314859373256780773 2106449121536132485646395)
                      ·
                        rfl

theorem cell23_4102295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 3, 1, 1, 1, 4].length) (baseStart_4102295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4102295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4102295 prefixEnd_4102295 := by exact prefixLift 4102295
  have htrace : WordTrace (prefixWord ++ tailWord_4102295) baseStart_4102295 baseEnd_4102295 := by
    simpa [prefixWord, tailWord_4102295, baseEnd_4102295] using wordTrace_append hprefix tailTrace_4102295
  have hstable : (prefixWord ++ tailWord_4102295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102295).length < 2 ^ (prefixWord ++ tailWord_4102295).sum := by decide
  have hdescent : baseEnd_4102295 < baseStart_4102295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102325 : List Nat := [1, 3, 3, 4, 1, 1, 2, 1, 1, 2, 4]
def baseStart_4102325 : Nat := 118140960795 + 4102325 * 2 ^ 59
def prefixEnd_4102325 : Nat := 4983230072969 + 3 ^ 40 * 4102325 * 2
def baseEnd_4102325 : Nat := 2106464525955767368271257

theorem tailTrace_4102325 : CollatzResearch.WordTrace tailWord_4102325 prefixEnd_4102325 2106464525955767368271257 := by
  unfold tailWord_4102325
  simp only [CollatzResearch.WordTrace]
  refine ⟨149624084862984621175796429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99749389908656414117197619 149624084862984621175796429)
  ·
    refine ⟨56109031823619232940923661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149624084862984621175796429 56109031823619232940923661)
    ·
      refine ⟨21040886933857212352846373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56109031823619232940923661 21040886933857212352846373)
      ·
        refine ⟨3945166300098227316158695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21040886933857212352846373 3945166300098227316158695)
        ·
          refine ⟨5917749450147340974238043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3945166300098227316158695 5917749450147340974238043)
          ·
            refine ⟨8876624175221011461357065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5917749450147340974238043 8876624175221011461357065)
            ·
              refine ⟨6657468131415758596017799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8876624175221011461357065 6657468131415758596017799)
              ·
                refine ⟨9986202197123637894026699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6657468131415758596017799 9986202197123637894026699)
                ·
                  refine ⟨14979303295685456841040049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9986202197123637894026699 14979303295685456841040049)
                  ·
                    refine ⟨11234477471764092630780037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14979303295685456841040049 11234477471764092630780037)
                    ·
                      refine ⟨2106464525955767368271257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11234477471764092630780037 2106464525955767368271257)
                      ·
                        rfl

theorem cell23_4102325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_4102325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4102325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4102325 prefixEnd_4102325 := by exact prefixLift 4102325
  have htrace : WordTrace (prefixWord ++ tailWord_4102325) baseStart_4102325 baseEnd_4102325 := by
    simpa [prefixWord, tailWord_4102325, baseEnd_4102325] using wordTrace_append hprefix tailTrace_4102325
  have hstable : (prefixWord ++ tailWord_4102325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102325).length < 2 ^ (prefixWord ++ tailWord_4102325).sum := by decide
  have hdescent : baseEnd_4102325 < baseStart_4102325 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102328 : List Nat := [2, 1, 2, 1, 2, 1, 3, 5, 2, 1, 3]
def baseStart_4102328 : Nat := 118140960795 + 4102328 * 2 ^ 59
def prefixEnd_4102328 : Nat := 4983230072969 + 3 ^ 40 * 4102328 * 2
def baseEnd_4102328 : Nat := 2106466066397730856533743

theorem tailTrace_4102328 : CollatzResearch.WordTrace tailWord_4102328 prefixEnd_4102328 2106466066397730856533743 := by
  unfold tailWord_4102328
  simp only [CollatzResearch.WordTrace]
  refine ⟨74812097140986876344077819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99749462854649168458770425 74812097140986876344077819)
  ·
    refine ⟨112218145711480314516116729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74812097140986876344077819 112218145711480314516116729)
    ·
      refine ⟨84163609283610235887087547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112218145711480314516116729 84163609283610235887087547)
      ·
        refine ⟨126245413925415353830631321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84163609283610235887087547 126245413925415353830631321)
        ·
          refine ⟨94684060444061515372973491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126245413925415353830631321 94684060444061515372973491)
          ·
            refine ⟨142026090666092273059460237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94684060444061515372973491 142026090666092273059460237)
            ·
              refine ⟨53259783999784602397297589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142026090666092273059460237 53259783999784602397297589)
              ·
                refine ⟨4993104749979806474746649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53259783999784602397297589 4993104749979806474746649)
                ·
                  refine ⟨3744828562484854856059987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4993104749979806474746649 3744828562484854856059987)
                  ·
                    refine ⟨5617242843727282284089981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3744828562484854856059987 5617242843727282284089981)
                    ·
                      refine ⟨2106466066397730856533743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5617242843727282284089981 2106466066397730856533743)
                      ·
                        rfl

theorem cell23_4102328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 5, 2, 1, 3].length) (baseStart_4102328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4102328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4102328 prefixEnd_4102328 := by exact prefixLift 4102328
  have htrace : WordTrace (prefixWord ++ tailWord_4102328) baseStart_4102328 baseEnd_4102328 := by
    simpa [prefixWord, tailWord_4102328, baseEnd_4102328] using wordTrace_append hprefix tailTrace_4102328
  have hstable : (prefixWord ++ tailWord_4102328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102328).length < 2 ^ (prefixWord ++ tailWord_4102328).sum := by decide
  have hdescent : baseEnd_4102328 < baseStart_4102328 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102344 : List Nat := [2, 1, 3, 1, 2, 1, 1, 1, 3, 8]
def baseStart_4102344 : Nat := 118140960795 + 4102344 * 2 ^ 59
def prefixEnd_4102344 : Nat := 4983230072969 + 3 ^ 40 * 4102344 * 2
def baseEnd_4102344 : Nat := 702158094029400931311223

theorem tailTrace_4102344 : CollatzResearch.WordTrace tailWord_4102344 prefixEnd_4102344 702158094029400931311223 := by
  unfold tailWord_4102344
  simp only [CollatzResearch.WordTrace]
  refine ⟨74812388924957893710369043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99749851899943858280492057 74812388924957893710369043)
  ·
    refine ⟨112218583387436840565553565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74812388924957893710369043 112218583387436840565553565)
    ·
      refine ⟨42081968770288815212082587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112218583387436840565553565 42081968770288815212082587)
      ·
        refine ⟨63122953155433222818123881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42081968770288815212082587 63122953155433222818123881)
        ·
          refine ⟨47342214866574917113592911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63122953155433222818123881 47342214866574917113592911)
          ·
            refine ⟨71013322299862375670389367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47342214866574917113592911 71013322299862375670389367)
            ·
              refine ⟨106519983449793563505584051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71013322299862375670389367 106519983449793563505584051)
              ·
                refine ⟨159779975174690345258376077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106519983449793563505584051 159779975174690345258376077)
                ·
                  refine ⟨59917490690508879471891029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 159779975174690345258376077 59917490690508879471891029)
                  ·
                    refine ⟨702158094029400931311223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 59917490690508879471891029 702158094029400931311223)
                    ·
                      rfl

theorem cell23_4102344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 3, 8].length) (baseStart_4102344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4102344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4102344 prefixEnd_4102344 := by exact prefixLift 4102344
  have htrace : WordTrace (prefixWord ++ tailWord_4102344) baseStart_4102344 baseEnd_4102344 := by
    simpa [prefixWord, tailWord_4102344, baseEnd_4102344] using wordTrace_append hprefix tailTrace_4102344
  have hstable : (prefixWord ++ tailWord_4102344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102344).length < 2 ^ (prefixWord ++ tailWord_4102344).sum := by decide
  have hdescent : baseEnd_4102344 < baseStart_4102344 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102384 : List Nat := [2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 9]
def baseStart_4102384 : Nat := 118140960795 + 4102384 * 2 ^ 59
def prefixEnd_4102384 : Nat := 4983230072969 + 3 ^ 40 * 4102384 * 2
def baseEnd_4102384 : Nat := 2106494821314382637433485

theorem tailTrace_4102384 : CollatzResearch.WordTrace tailWord_4102384 prefixEnd_4102384 2106494821314382637433485 := by
  unfold tailWord_4102384
  simp only [CollatzResearch.WordTrace]
  refine ⟨74813118384885437126097103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99750824513180582834796137 74813118384885437126097103)
  ·
    refine ⟨112219677577328155689145655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74813118384885437126097103 112219677577328155689145655)
    ·
      refine ⟨168329516365992233533718483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112219677577328155689145655 168329516365992233533718483)
      ·
        refine ⟨252494274548988350300577725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168329516365992233533718483 252494274548988350300577725)
        ·
          refine ⟨94685352955870631362716647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252494274548988350300577725 94685352955870631362716647)
          ·
            refine ⟨142028029433805947044074971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94685352955870631362716647 142028029433805947044074971)
            ·
              refine ⟨213042044150708920566112457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142028029433805947044074971 213042044150708920566112457)
              ·
                refine ⟨159781533113031690424584343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213042044150708920566112457 159781533113031690424584343)
                ·
                  refine ⟨239672299669547535636876515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 159781533113031690424584343 239672299669547535636876515)
                  ·
                    refine ⟨359508449504321303455314773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 239672299669547535636876515 359508449504321303455314773)
                    ·
                      refine ⟨2106494821314382637433485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 359508449504321303455314773 2106494821314382637433485)
                      ·
                        rfl

theorem cell23_4102384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 9].length) (baseStart_4102384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4102384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4102384 prefixEnd_4102384 := by exact prefixLift 4102384
  have htrace : WordTrace (prefixWord ++ tailWord_4102384) baseStart_4102384 baseEnd_4102384 := by
    simpa [prefixWord, tailWord_4102384, baseEnd_4102384] using wordTrace_append hprefix tailTrace_4102384
  have hstable : (prefixWord ++ tailWord_4102384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102384).length < 2 ^ (prefixWord ++ tailWord_4102384).sum := by decide
  have hdescent : baseEnd_4102384 < baseStart_4102384 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102385 : List Nat := [1, 2, 2, 2, 2, 1, 2, 5, 2, 2, 2]
def baseStart_4102385 : Nat := 118140960795 + 4102385 * 2 ^ 59
def prefixEnd_4102385 : Nat := 4983230072969 + 3 ^ 40 * 4102385 * 2
def baseEnd_4102385 : Nat := 2106495334795037133520981

theorem tailTrace_4102385 : CollatzResearch.WordTrace tailWord_4102385 prefixEnd_4102385 2106495334795037133520981 := by
  unfold tailWord_4102385
  simp only [CollatzResearch.WordTrace]
  refine ⟨149626273242767251422980609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99750848828511500948653739 149626273242767251422980609)
  ·
    refine ⟨112219704932075438567235457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149626273242767251422980609 112219704932075438567235457)
    ·
      refine ⟨84164778699056578925426593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112219704932075438567235457 84164778699056578925426593)
      ·
        refine ⟨63123584024292434194069945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84164778699056578925426593 63123584024292434194069945)
        ·
          refine ⟨47342688018219325645552459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63123584024292434194069945 47342688018219325645552459)
          ·
            refine ⟨71014032027328988468328689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47342688018219325645552459 71014032027328988468328689)
            ·
              refine ⟨53260524020496741351246517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71014032027328988468328689 53260524020496741351246517)
              ·
                refine ⟨4993174126921569501679361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53260524020496741351246517 4993174126921569501679361)
                ·
                  refine ⟨3744880595191177126259521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4993174126921569501679361 3744880595191177126259521)
                  ·
                    refine ⟨2808660446393382844694641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3744880595191177126259521 2808660446393382844694641)
                    ·
                      refine ⟨2106495334795037133520981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2808660446393382844694641 2106495334795037133520981)
                      ·
                        rfl

theorem cell23_4102385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 5, 2, 2, 2].length) (baseStart_4102385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4102385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4102385 prefixEnd_4102385 := by exact prefixLift 4102385
  have htrace : WordTrace (prefixWord ++ tailWord_4102385) baseStart_4102385 baseEnd_4102385 := by
    simpa [prefixWord, tailWord_4102385, baseEnd_4102385] using wordTrace_append hprefix tailTrace_4102385
  have hstable : (prefixWord ++ tailWord_4102385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102385).length < 2 ^ (prefixWord ++ tailWord_4102385).sum := by decide
  have hdescent : baseEnd_4102385 < baseStart_4102385 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102402 : List Nat := [3, 4, 1, 1, 2, 1, 1, 2, 4, 2, 2]
def baseStart_4102402 : Nat := 118140960795 + 4102402 * 2 ^ 59
def prefixEnd_4102402 : Nat := 4983230072969 + 3 ^ 40 * 4102402 * 2
def baseEnd_4102402 : Nat := 2106504063966163567008403

theorem tailTrace_4102402 : CollatzResearch.WordTrace tailWord_4102402 prefixEnd_4102402 2106504063966163567008403 := by
  unfold tailWord_4102402
  simp only [CollatzResearch.WordTrace]
  refine ⟨37406723320926415831587365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99751262189137108884232973 37406723320926415831587365)
  ·
    refine ⟨7013760622673702968422631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37406723320926415831587365 7013760622673702968422631)
    ·
      refine ⟨10520640934010554452633947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7013760622673702968422631 10520640934010554452633947)
      ·
        refine ⟨15780961401015831678950921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10520640934010554452633947 15780961401015831678950921)
        ·
          refine ⟨11835721050761873759213191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15780961401015831678950921 11835721050761873759213191)
          ·
            refine ⟨17753581576142810638819787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11835721050761873759213191 17753581576142810638819787)
            ·
              refine ⟨26630372364214215958229681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17753581576142810638819787 26630372364214215958229681)
              ·
                refine ⟨19972779273160661968672261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26630372364214215958229681 19972779273160661968672261)
                ·
                  refine ⟨3744896113717624119126049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19972779273160661968672261 3744896113717624119126049)
                  ·
                    refine ⟨2808672085288218089344537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3744896113717624119126049 2808672085288218089344537)
                    ·
                      refine ⟨2106504063966163567008403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2808672085288218089344537 2106504063966163567008403)
                      ·
                        rfl

theorem cell23_4102402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 4, 2, 2].length) (baseStart_4102402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4102402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4102402 prefixEnd_4102402 := by exact prefixLift 4102402
  have htrace : WordTrace (prefixWord ++ tailWord_4102402) baseStart_4102402 baseEnd_4102402 := by
    simpa [prefixWord, tailWord_4102402, baseEnd_4102402] using wordTrace_append hprefix tailTrace_4102402
  have hstable : (prefixWord ++ tailWord_4102402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102402).length < 2 ^ (prefixWord ++ tailWord_4102402).sum := by decide
  have hdescent : baseEnd_4102402 < baseStart_4102402 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102421 : List Nat := [1, 3, 2, 1, 2, 1, 3, 1, 4, 5]
def baseStart_4102421 : Nat := 118140960795 + 4102421 * 2 ^ 59
def prefixEnd_4102421 : Nat := 4983230072969 + 3 ^ 40 * 4102421 * 2
def baseEnd_4102421 : Nat := 702171273366199664223605

theorem tailTrace_4102421 : CollatzResearch.WordTrace tailWord_4102421 prefixEnd_4102421 702171273366199664223605 := by
  unfold tailWord_4102421
  simp only [CollatzResearch.WordTrace]
  refine ⟨149627586270636829571291117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99751724180424553047527411 149627586270636829571291117)
  ·
    refine ⟨56110344851488811089234169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149627586270636829571291117 56110344851488811089234169)
    ·
      refine ⟨42082758638616608316925627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56110344851488811089234169 42082758638616608316925627)
      ·
        refine ⟨63124137957924912475388441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42082758638616608316925627 63124137957924912475388441)
        ·
          refine ⟨47343103468443684356541331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63124137957924912475388441 47343103468443684356541331)
          ·
            refine ⟨71014655202665526534811997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47343103468443684356541331 71014655202665526534811997)
            ·
              refine ⟨26630495700999572450554499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71014655202665526534811997 26630495700999572450554499)
              ·
                refine ⟨39945743551499358675831749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26630495700999572450554499 39945743551499358675831749)
                ·
                  refine ⟨7489826915906129751718453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39945743551499358675831749 7489826915906129751718453)
                  ·
                    refine ⟨702171273366199664223605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7489826915906129751718453 702171273366199664223605)
                    ·
                      rfl

theorem cell23_4102421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 4, 5].length) (baseStart_4102421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4102421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4102421 prefixEnd_4102421 := by exact prefixLift 4102421
  have htrace : WordTrace (prefixWord ++ tailWord_4102421) baseStart_4102421 baseEnd_4102421 := by
    simpa [prefixWord, tailWord_4102421, baseEnd_4102421] using wordTrace_append hprefix tailTrace_4102421
  have hstable : (prefixWord ++ tailWord_4102421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102421).length < 2 ^ (prefixWord ++ tailWord_4102421).sum := by decide
  have hdescent : baseEnd_4102421 < baseStart_4102421 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102428 : List Nat := [2, 2, 3, 1, 1, 1, 1, 3, 2, 5, 2]
def baseStart_4102428 : Nat := 118140960795 + 4102428 * 2 ^ 59
def prefixEnd_4102428 : Nat := 4983230072969 + 3 ^ 40 * 4102428 * 2
def baseEnd_4102428 : Nat := 2106517414463180465283283

theorem tailTrace_4102428 : CollatzResearch.WordTrace tailWord_4102428 prefixEnd_4102428 2106517414463180465283283 := by
  unfold tailWord_4102428
  simp only [CollatzResearch.WordTrace]
  refine ⟨74813920790805734883397969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99751894387740979844530625 74813920790805734883397969)
  ·
    refine ⟨56110440593104301162548477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74813920790805734883397969 56110440593104301162548477)
    ·
      refine ⟨21041415222414112935955679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56110440593104301162548477 21041415222414112935955679)
      ·
        refine ⟨31562122833621169403933519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21041415222414112935955679 31562122833621169403933519)
        ·
          refine ⟨47343184250431754105900279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31562122833621169403933519 47343184250431754105900279)
          ·
            refine ⟨71014776375647631158850419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47343184250431754105900279 71014776375647631158850419)
            ·
              refine ⟨106522164563471446738275629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71014776375647631158850419 106522164563471446738275629)
              ·
                refine ⟨39945811711301792526853361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106522164563471446738275629 39945811711301792526853361)
                ·
                  refine ⟨29959358783476344395140021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39945811711301792526853361 29959358783476344395140021)
                  ·
                    refine ⟨2808689885950907287044377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29959358783476344395140021 2808689885950907287044377)
                    ·
                      refine ⟨2106517414463180465283283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2808689885950907287044377 2106517414463180465283283)
                      ·
                        rfl

theorem cell23_4102428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 2, 5, 2].length) (baseStart_4102428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4102428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4102428 prefixEnd_4102428 := by exact prefixLift 4102428
  have htrace : WordTrace (prefixWord ++ tailWord_4102428) baseStart_4102428 baseEnd_4102428 := by
    simpa [prefixWord, tailWord_4102428, baseEnd_4102428] using wordTrace_append hprefix tailTrace_4102428
  have hstable : (prefixWord ++ tailWord_4102428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102428).length < 2 ^ (prefixWord ++ tailWord_4102428).sum := by decide
  have hdescent : baseEnd_4102428 < baseStart_4102428 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102431 : List Nat := [1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 7]
def baseStart_4102431 : Nat := 118140960795 + 4102431 * 2 ^ 59
def prefixEnd_4102431 : Nat := 4983230072969 + 3 ^ 40 * 4102431 * 2
def baseEnd_4102431 : Nat := 2106518954905143953545769

theorem tailTrace_4102431 : CollatzResearch.WordTrace tailWord_4102431 prefixEnd_4102431 2106518954905143953545769 := by
  unfold tailWord_4102431
  simp only [CollatzResearch.WordTrace]
  refine ⟨149627951000600601279155147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99751967333733734186103431 149627951000600601279155147)
  ·
    refine ⟨224441926500900901918732721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149627951000600601279155147 224441926500900901918732721)
    ·
      refine ⟨168331444875675676439049541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224441926500900901918732721 168331444875675676439049541)
      ·
        refine ⟨31562145914189189332321789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168331444875675676439049541 31562145914189189332321789)
        ·
          refine ⟨11835804717820945999620671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31562145914189189332321789 11835804717820945999620671)
          ·
            refine ⟨17753707076731418999431007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11835804717820945999620671 17753707076731418999431007)
            ·
              refine ⟨26630560615097128499146511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17753707076731418999431007 26630560615097128499146511)
              ·
                refine ⟨39945840922645692748719767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26630560615097128499146511 39945840922645692748719767)
                ·
                  refine ⟨59918761383968539123079651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39945840922645692748719767 59918761383968539123079651)
                  ·
                    refine ⟨89878142075952808684619477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59918761383968539123079651 89878142075952808684619477)
                    ·
                      refine ⟨2106518954905143953545769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 89878142075952808684619477 2106518954905143953545769)
                      ·
                        rfl

theorem cell23_4102431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_4102431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4102431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4102431 prefixEnd_4102431 := by exact prefixLift 4102431
  have htrace : WordTrace (prefixWord ++ tailWord_4102431) baseStart_4102431 baseEnd_4102431 := by
    simpa [prefixWord, tailWord_4102431, baseEnd_4102431] using wordTrace_append hprefix tailTrace_4102431
  have hstable : (prefixWord ++ tailWord_4102431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102431).length < 2 ^ (prefixWord ++ tailWord_4102431).sum := by decide
  have hdescent : baseEnd_4102431 < baseStart_4102431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102458 : List Nat := [3, 1, 1, 1, 4, 2, 1, 3, 2, 1, 4]
def baseStart_4102458 : Nat := 118140960795 + 4102458 * 2 ^ 59
def prefixEnd_4102458 : Nat := 4983230072969 + 3 ^ 40 * 4102458 * 2
def baseEnd_4102458 : Nat := 2106532818882815347908145

theorem tailTrace_4102458 : CollatzResearch.WordTrace tailWord_4102458 prefixEnd_4102458 2106532818882815347908145 := by
  unfold tailWord_4102458
  simp only [CollatzResearch.WordTrace]
  refine ⟨37407233942875696222597007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99752623847668523260258685 37407233942875696222597007)
  ·
    refine ⟨56110850914313544333895511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37407233942875696222597007 56110850914313544333895511)
    ·
      refine ⟨84166276371470316500843267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56110850914313544333895511 84166276371470316500843267)
      ·
        refine ⟨126249414557205474751264901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84166276371470316500843267 126249414557205474751264901)
        ·
          refine ⟨23671765229476026515862169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126249414557205474751264901 23671765229476026515862169)
          ·
            refine ⟨17753823922107019886896627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23671765229476026515862169 17753823922107019886896627)
            ·
              refine ⟨26630735883160529830344941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17753823922107019886896627 26630735883160529830344941)
              ·
                refine ⟨9986525956185198686379353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26630735883160529830344941 9986525956185198686379353)
                ·
                  refine ⟨7489894467138899014784515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9986525956185198686379353 7489894467138899014784515)
                  ·
                    refine ⟨11234841700708348522176773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7489894467138899014784515 11234841700708348522176773)
                    ·
                      refine ⟨2106532818882815347908145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11234841700708348522176773 2106532818882815347908145)
                      ·
                        rfl

theorem cell23_4102458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 3, 2, 1, 4].length) (baseStart_4102458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4102458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4102458 prefixEnd_4102458 := by exact prefixLift 4102458
  have htrace : WordTrace (prefixWord ++ tailWord_4102458) baseStart_4102458 baseEnd_4102458 := by
    simpa [prefixWord, tailWord_4102458, baseEnd_4102458] using wordTrace_append hprefix tailTrace_4102458
  have hstable : (prefixWord ++ tailWord_4102458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102458).length < 2 ^ (prefixWord ++ tailWord_4102458).sum := by decide
  have hdescent : baseEnd_4102458 < baseStart_4102458 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102471 : List Nat := [1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 6]
def baseStart_4102471 : Nat := 118140960795 + 4102471 * 2 ^ 59
def prefixEnd_4102471 : Nat := 4983230072969 + 3 ^ 40 * 4102471 * 2
def baseEnd_4102471 : Nat := 2106539494131323797045585

theorem tailTrace_4102471 : CollatzResearch.WordTrace tailWord_4102471 prefixEnd_4102471 2106539494131323797045585 := by
  unfold tailWord_4102471
  simp only [CollatzResearch.WordTrace]
  refine ⟨149629409920455688110611267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99752939946970458740407511 149629409920455688110611267)
  ·
    refine ⟨224444114880683532165916901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149629409920455688110611267 224444114880683532165916901)
    ·
      refine ⟨42083271540128162281109419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 224444114880683532165916901 42083271540128162281109419)
      ·
        refine ⟨63124907310192243421664129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42083271540128162281109419 63124907310192243421664129)
        ·
          refine ⟨47343680482644182566248097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63124907310192243421664129 47343680482644182566248097)
          ·
            refine ⟨35507760361983136924686073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47343680482644182566248097 35507760361983136924686073)
            ·
              refine ⟨26630820271487352693514555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35507760361983136924686073 26630820271487352693514555)
              ·
                refine ⟨39946230407231029040271833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26630820271487352693514555 39946230407231029040271833)
                ·
                  refine ⟨29959672805423271780203875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39946230407231029040271833 29959672805423271780203875)
                  ·
                    refine ⟨44939509208134907670305813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29959672805423271780203875 44939509208134907670305813)
                    ·
                      refine ⟨2106539494131323797045585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44939509208134907670305813 2106539494131323797045585)
                      ·
                        rfl

theorem cell23_4102471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_4102471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4102471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4102471 prefixEnd_4102471 := by exact prefixLift 4102471
  have htrace : WordTrace (prefixWord ++ tailWord_4102471) baseStart_4102471 baseEnd_4102471 := by
    simpa [prefixWord, tailWord_4102471, baseEnd_4102471] using wordTrace_append hprefix tailTrace_4102471
  have hstable : (prefixWord ++ tailWord_4102471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102471).length < 2 ^ (prefixWord ++ tailWord_4102471).sum := by decide
  have hdescent : baseEnd_4102471 < baseStart_4102471 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102478 : List Nat := [4, 1, 1, 1, 1, 1, 2, 3, 4, 2, 3]
def baseStart_4102478 : Nat := 118140960795 + 4102478 * 2 ^ 59
def prefixEnd_4102478 : Nat := 4983230072969 + 3 ^ 40 * 4102478 * 2
def baseEnd_4102478 : Nat := 2106543088495905269658053

theorem tailTrace_4102478 : CollatzResearch.WordTrace tailWord_4102478 prefixEnd_4102478 2106543088495905269658053 := by
  unfold tailWord_4102478
  simp only [CollatzResearch.WordTrace]
  refine ⟨18703708153928791038264511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99753110154286885537410725 18703708153928791038264511)
  ·
    refine ⟨28055562230893186557396767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18703708153928791038264511 28055562230893186557396767)
    ·
      refine ⟨42083343346339779836095151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28055562230893186557396767 42083343346339779836095151)
      ·
        refine ⟨63125015019509669754142727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42083343346339779836095151 63125015019509669754142727)
        ·
          refine ⟨94687522529264504631214091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63125015019509669754142727 94687522529264504631214091)
          ·
            refine ⟨142031283793896756946821137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94687522529264504631214091 142031283793896756946821137)
            ·
              refine ⟨106523462845422567710115853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142031283793896756946821137 106523462845422567710115853)
              ·
                refine ⟨39946298567033462891293445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106523462845422567710115853 39946298567033462891293445)
                ·
                  refine ⟨7489930981318774292117521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39946298567033462891293445 7489930981318774292117521)
                  ·
                    refine ⟨5617448235989080719088141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7489930981318774292117521 5617448235989080719088141)
                    ·
                      refine ⟨2106543088495905269658053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5617448235989080719088141 2106543088495905269658053)
                      ·
                        rfl

theorem cell23_4102478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 4, 2, 3].length) (baseStart_4102478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4102478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4102478 prefixEnd_4102478 := by exact prefixLift 4102478
  have htrace : WordTrace (prefixWord ++ tailWord_4102478) baseStart_4102478 baseEnd_4102478 := by
    simpa [prefixWord, tailWord_4102478, baseEnd_4102478] using wordTrace_append hprefix tailTrace_4102478
  have hstable : (prefixWord ++ tailWord_4102478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102478).length < 2 ^ (prefixWord ++ tailWord_4102478).sum := by decide
  have hdescent : baseEnd_4102478 < baseStart_4102478 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102521 : List Nat := [1, 2, 1, 3, 2, 1, 1, 1, 2, 4, 5]
def baseStart_4102521 : Nat := 118140960795 + 4102521 * 2 ^ 59
def prefixEnd_4102521 : Nat := 4983230072969 + 3 ^ 40 * 4102521 * 2
def baseEnd_4102521 : Nat := 2106565168164048601420355

theorem tailTrace_4102521 : CollatzResearch.WordTrace tailWord_4102521 prefixEnd_4102521 2106565168164048601420355 := by
  unfold tailWord_4102521
  simp only [CollatzResearch.WordTrace]
  refine ⟨149631233570274546649931417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99754155713516364433287611 149631233570274546649931417)
  ·
    refine ⟨112223425177705909987448563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149631233570274546649931417 112223425177705909987448563)
    ·
      refine ⟨168335137766558864981172845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112223425177705909987448563 168335137766558864981172845)
      ·
        refine ⟨63125676662459574367939817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168335137766558864981172845 63125676662459574367939817)
        ·
          refine ⟨47344257496844680775954863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63125676662459574367939817 47344257496844680775954863)
          ·
            refine ⟨71016386245267021163932295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47344257496844680775954863 71016386245267021163932295)
            ·
              refine ⟨106524579367900531745898443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71016386245267021163932295 106524579367900531745898443)
              ·
                refine ⟨159786869051850797618847665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106524579367900531745898443 159786869051850797618847665)
                ·
                  refine ⟨119840151788888098214135749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159786869051850797618847665 119840151788888098214135749)
                  ·
                    refine ⟨22470028460416518415150453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 119840151788888098214135749 22470028460416518415150453)
                    ·
                      refine ⟨2106565168164048601420355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22470028460416518415150453 2106565168164048601420355)
                      ·
                        rfl

theorem cell23_4102521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_4102521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4102521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4102521 prefixEnd_4102521 := by exact prefixLift 4102521
  have htrace : WordTrace (prefixWord ++ tailWord_4102521) baseStart_4102521 baseEnd_4102521 := by
    simpa [prefixWord, tailWord_4102521, baseEnd_4102521] using wordTrace_append hprefix tailTrace_4102521
  have hstable : (prefixWord ++ tailWord_4102521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102521).length < 2 ^ (prefixWord ++ tailWord_4102521).sum := by decide
  have hdescent : baseEnd_4102521 < baseStart_4102521 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102535 : List Nat := [1, 1, 4, 2, 2, 1, 2, 1, 4, 3, 2]
def baseStart_4102535 : Nat := 118140960795 + 4102535 * 2 ^ 59
def prefixEnd_4102535 : Nat := 4983230072969 + 3 ^ 40 * 4102535 * 2
def baseEnd_4102535 : Nat := 2106572356893211546645291

theorem tailTrace_4102535 : CollatzResearch.WordTrace tailWord_4102535 prefixEnd_4102535 2106572356893211546645291 := by
  unfold tailWord_4102535
  simp only [CollatzResearch.WordTrace]
  refine ⟨149631744192223827040941059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99754496128149218027294039 149631744192223827040941059)
  ·
    refine ⟨224447616288335740561411589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149631744192223827040941059 224447616288335740561411589)
    ·
      refine ⟨42083928054062951355264673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 224447616288335740561411589 42083928054062951355264673)
      ·
        refine ⟨31562946040547213516448505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42083928054062951355264673 31562946040547213516448505)
        ·
          refine ⟨23672209530410410137336379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31562946040547213516448505 23672209530410410137336379)
          ·
            refine ⟨35508314295615615206004569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23672209530410410137336379 35508314295615615206004569)
            ·
              refine ⟨26631235721711711404503427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35508314295615615206004569 26631235721711711404503427)
              ·
                refine ⟨39946853582567567106755141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26631235721711711404503427 39946853582567567106755141)
                ·
                  refine ⟨7490035046731418832516589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39946853582567567106755141 7490035046731418832516589)
                  ·
                    refine ⟨2808763142524282062193721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7490035046731418832516589 2808763142524282062193721)
                    ·
                      refine ⟨2106572356893211546645291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2808763142524282062193721 2106572356893211546645291)
                      ·
                        rfl

theorem cell23_4102535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 4, 3, 2].length) (baseStart_4102535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4102535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4102535 prefixEnd_4102535 := by exact prefixLift 4102535
  have htrace : WordTrace (prefixWord ++ tailWord_4102535) baseStart_4102535 baseEnd_4102535 := by
    simpa [prefixWord, tailWord_4102535, baseEnd_4102535] using wordTrace_append hprefix tailTrace_4102535
  have hstable : (prefixWord ++ tailWord_4102535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102535).length < 2 ^ (prefixWord ++ tailWord_4102535).sum := by decide
  have hdescent : baseEnd_4102535 < baseStart_4102535 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102542 : List Nat := [4, 1, 1, 4, 1, 1, 1, 3, 3, 1, 3]
def baseStart_4102542 : Nat := 118140960795 + 4102542 * 2 ^ 59
def prefixEnd_4102542 : Nat := 4983230072969 + 3 ^ 40 * 4102542 * 2
def baseEnd_4102542 : Nat := 2106575951257793019257759

theorem tailTrace_4102542 : CollatzResearch.WordTrace tailWord_4102542 prefixEnd_4102542 2106575951257793019257759 := by
  unfold tailWord_4102542
  simp only [CollatzResearch.WordTrace]
  refine ⟨18703999937899808404555735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99754666335465644824297253 18703999937899808404555735)
  ·
    refine ⟨28055999906849712606833603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18703999937899808404555735 28055999906849712606833603)
    ·
      refine ⟨42083999860274568910250405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28055999906849712606833603 42083999860274568910250405)
      ·
        refine ⟨7890749973801481670671951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42083999860274568910250405 7890749973801481670671951)
        ·
          refine ⟨11836124960702222506007927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7890749973801481670671951 11836124960702222506007927)
          ·
            refine ⟨17754187441053333759011891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11836124960702222506007927 17754187441053333759011891)
            ·
              refine ⟨26631281161580000638517837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17754187441053333759011891 26631281161580000638517837)
              ·
                refine ⟨9986730435592500239444189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26631281161580000638517837 9986730435592500239444189)
                ·
                  refine ⟨3745023913347187589791571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9986730435592500239444189 3745023913347187589791571)
                  ·
                    refine ⟨5617535870020781384687357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3745023913347187589791571 5617535870020781384687357)
                    ·
                      refine ⟨2106575951257793019257759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5617535870020781384687357 2106575951257793019257759)
                      ·
                        rfl

theorem cell23_4102542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_4102542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4102542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4102542 prefixEnd_4102542 := by exact prefixLift 4102542
  have htrace : WordTrace (prefixWord ++ tailWord_4102542) baseStart_4102542 baseEnd_4102542 := by
    simpa [prefixWord, tailWord_4102542, baseEnd_4102542] using wordTrace_append hprefix tailTrace_4102542
  have hstable : (prefixWord ++ tailWord_4102542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102542).length < 2 ^ (prefixWord ++ tailWord_4102542).sum := by decide
  have hdescent : baseEnd_4102542 < baseStart_4102542 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102565 : List Nat := [1, 3, 1, 2, 1, 1, 6, 2, 1, 1, 4]
def baseStart_4102565 : Nat := 118140960795 + 4102565 * 2 ^ 59
def prefixEnd_4102565 : Nat := 4983230072969 + 3 ^ 40 * 4102565 * 2
def baseEnd_4102565 : Nat := 2106587761312846429270153

theorem tailTrace_4102565 : CollatzResearch.WordTrace tailWord_4102565 prefixEnd_4102565 2106587761312846429270153 := by
  unfold tailWord_4102565
  simp only [CollatzResearch.WordTrace]
  refine ⟨149632838382115142164533149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99755225588076761443022099 149632838382115142164533149)
  ·
    refine ⟨56112314393293178311699931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149632838382115142164533149 56112314393293178311699931)
    ·
      refine ⟨84168471589939767467549897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56112314393293178311699931 84168471589939767467549897)
      ·
        refine ⟨63126353692454825600662423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84168471589939767467549897 63126353692454825600662423)
        ·
          refine ⟨94689530538682238400993635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63126353692454825600662423 94689530538682238400993635)
          ·
            refine ⟨142034295808023357601490453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94689530538682238400993635 142034295808023357601490453)
            ·
              refine ⟨6657857616001094887569865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 142034295808023357601490453 6657857616001094887569865)
              ·
                refine ⟨4993393212000821165677399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6657857616001094887569865 4993393212000821165677399)
                ·
                  refine ⟨7490089818001231748516099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4993393212000821165677399 7490089818001231748516099)
                  ·
                    refine ⟨11235134727001847622774149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7490089818001231748516099 11235134727001847622774149)
                    ·
                      refine ⟨2106587761312846429270153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11235134727001847622774149 2106587761312846429270153)
                      ·
                        rfl

theorem cell23_4102565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 2, 1, 1, 4].length) (baseStart_4102565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4102565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4102565 prefixEnd_4102565 := by exact prefixLift 4102565
  have htrace : WordTrace (prefixWord ++ tailWord_4102565) baseStart_4102565 baseEnd_4102565 := by
    simpa [prefixWord, tailWord_4102565, baseEnd_4102565] using wordTrace_append hprefix tailTrace_4102565
  have hstable : (prefixWord ++ tailWord_4102565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102565).length < 2 ^ (prefixWord ++ tailWord_4102565).sum := by decide
  have hdescent : baseEnd_4102565 < baseStart_4102565 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102570 : List Nat := [3, 1, 6, 1, 2, 1, 1, 3, 1, 4]
def baseStart_4102570 : Nat := 118140960795 + 4102570 * 2 ^ 59
def prefixEnd_4102570 : Nat := 4983230072969 + 3 ^ 40 * 4102570 * 2
def baseEnd_4102570 : Nat := 702196776238706303235877

theorem tailTrace_4102570 : CollatzResearch.WordTrace tailWord_4102570 prefixEnd_4102570 702196776238706303235877 := by
  unfold tailWord_4102570
  simp only [CollatzResearch.WordTrace]
  refine ⟨37408255186774257004616291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99755347164731352012310109 37408255186774257004616291)
  ·
    refine ⟨56112382780161385506924437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37408255186774257004616291 56112382780161385506924437)
    ·
      refine ⟨2630267942820064945637083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 56112382780161385506924437 2630267942820064945637083)
      ·
        refine ⟨3945401914230097418455625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2630267942820064945637083 3945401914230097418455625)
        ·
          refine ⟨2959051435672573063841719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3945401914230097418455625 2959051435672573063841719)
          ·
            refine ⟨4438577153508859595762579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2959051435672573063841719 4438577153508859595762579)
            ·
              refine ⟨6657865730263289393643869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4438577153508859595762579 6657865730263289393643869)
              ·
                refine ⟨2496699648848733522616451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6657865730263289393643869 2496699648848733522616451)
                ·
                  refine ⟨3745049473273100283924677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2496699648848733522616451 3745049473273100283924677)
                  ·
                    refine ⟨702196776238706303235877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3745049473273100283924677 702196776238706303235877)
                    ·
                      rfl

theorem cell23_4102570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_4102570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4102570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4102570 prefixEnd_4102570 := by exact prefixLift 4102570
  have htrace : WordTrace (prefixWord ++ tailWord_4102570) baseStart_4102570 baseEnd_4102570 := by
    simpa [prefixWord, tailWord_4102570, baseEnd_4102570] using wordTrace_append hprefix tailTrace_4102570
  have hstable : (prefixWord ++ tailWord_4102570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102570).length < 2 ^ (prefixWord ++ tailWord_4102570).sum := by decide
  have hdescent : baseEnd_4102570 < baseStart_4102570 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102578 : List Nat := [3, 2, 1, 1, 1, 1, 4, 1, 3, 2, 4]
def baseStart_4102578 : Nat := 118140960795 + 4102578 * 2 ^ 59
def prefixEnd_4102578 : Nat := 4983230072969 + 3 ^ 40 * 4102578 * 2
def baseEnd_4102578 : Nat := 2106594436561354878407593

theorem tailTrace_4102578 : CollatzResearch.WordTrace tailWord_4102578 prefixEnd_4102578 2106594436561354878407593 := by
  unfold tailWord_4102578
  simp only [CollatzResearch.WordTrace]
  refine ⟨37408328132767011346189097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99755541687378696923170925 37408328132767011346189097)
  ·
    refine ⟨28056246099575258509641823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37408328132767011346189097 28056246099575258509641823)
    ·
      refine ⟨42084369149362887764462735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28056246099575258509641823 42084369149362887764462735)
      ·
        refine ⟨63126553724044331646694103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42084369149362887764462735 63126553724044331646694103)
        ·
          refine ⟨94689830586066497470041155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63126553724044331646694103 94689830586066497470041155)
          ·
            refine ⟨142034745879099746205061733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94689830586066497470041155 142034745879099746205061733)
            ·
              refine ⟨26631514852331202413449075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142034745879099746205061733 26631514852331202413449075)
              ·
                refine ⟨39947272278496803620173613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26631514852331202413449075 39947272278496803620173613)
                ·
                  refine ⟨14980227104436301357565105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39947272278496803620173613 14980227104436301357565105)
                  ·
                    refine ⟨11235170328327226018173829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14980227104436301357565105 11235170328327226018173829)
                    ·
                      refine ⟨2106594436561354878407593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11235170328327226018173829 2106594436561354878407593)
                      ·
                        rfl

theorem cell23_4102578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 3, 2, 4].length) (baseStart_4102578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4102578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4102578 prefixEnd_4102578 := by exact prefixLift 4102578
  have htrace : WordTrace (prefixWord ++ tailWord_4102578) baseStart_4102578 baseEnd_4102578 := by
    simpa [prefixWord, tailWord_4102578, baseEnd_4102578] using wordTrace_append hprefix tailTrace_4102578
  have hstable : (prefixWord ++ tailWord_4102578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102578).length < 2 ^ (prefixWord ++ tailWord_4102578).sum := by decide
  have hdescent : baseEnd_4102578 < baseStart_4102578 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102585 : List Nat := [1, 2, 1, 4, 3, 2, 2, 1, 1, 1, 5]
def baseStart_4102585 : Nat := 118140960795 + 4102585 * 2 ^ 59
def prefixEnd_4102585 : Nat := 4983230072969 + 3 ^ 40 * 4102585 * 2
def baseEnd_4102585 : Nat := 2106598030925936351020061

theorem tailTrace_4102585 : CollatzResearch.WordTrace tailWord_4102585 prefixEnd_4102585 2106598030925936351020061 := by
  unfold tailWord_4102585
  simp only [CollatzResearch.WordTrace]
  refine ⟨149633567842042685580261209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99755711894695123720174139 149633567842042685580261209)
  ·
    refine ⟨112225175881532014185195907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149633567842042685580261209 112225175881532014185195907)
    ·
      refine ⟨168337763822298021277793861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112225175881532014185195907 168337763822298021277793861)
      ·
        refine ⟨31563330716680878989586349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168337763822298021277793861 31563330716680878989586349)
        ·
          refine ⟨11836249018755329621094881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31563330716680878989586349 11836249018755329621094881)
          ·
            refine ⟨8877186764066497215821161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11836249018755329621094881 8877186764066497215821161)
            ·
              refine ⟨6657890073049872911865871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8877186764066497215821161 6657890073049872911865871)
              ·
                refine ⟨9986835109574809367798807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6657890073049872911865871 9986835109574809367798807)
                ·
                  refine ⟨14980252664362214051698211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9986835109574809367798807 14980252664362214051698211)
                  ·
                    refine ⟨22470378996543321077547317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14980252664362214051698211 22470378996543321077547317)
                    ·
                      refine ⟨2106598030925936351020061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22470378996543321077547317 2106598030925936351020061)
                      ·
                        rfl

theorem cell23_4102585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 1, 1, 1, 5].length) (baseStart_4102585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4102585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4102585 prefixEnd_4102585 := by exact prefixLift 4102585
  have htrace : WordTrace (prefixWord ++ tailWord_4102585) baseStart_4102585 baseEnd_4102585 := by
    simpa [prefixWord, tailWord_4102585, baseEnd_4102585] using wordTrace_append hprefix tailTrace_4102585
  have hstable : (prefixWord ++ tailWord_4102585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102585).length < 2 ^ (prefixWord ++ tailWord_4102585).sum := by decide
  have hdescent : baseEnd_4102585 < baseStart_4102585 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102588 : List Nat := [2, 2, 2, 4, 1, 1, 11]
def baseStart_4102588 : Nat := 118140960795 + 4102588 * 2 ^ 59
def prefixEnd_4102588 : Nat := 4983230072969 + 3 ^ 40 * 4102588 * 2
def baseEnd_4102588 : Nat := 26007402115653084435587

theorem tailTrace_4102588 : CollatzResearch.WordTrace tailWord_4102588 prefixEnd_4102588 26007402115653084435587 := by
  unfold tailWord_4102588
  simp only [CollatzResearch.WordTrace]
  refine ⟨74816838630515908546310209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99755784840687878061746945 74816838630515908546310209)
  ·
    refine ⟨56112628972886931409732657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74816838630515908546310209 56112628972886931409732657)
    ·
      refine ⟨42084471729665198557299493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56112628972886931409732657 42084471729665198557299493)
      ·
        refine ⟨7890838449312224729493655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42084471729665198557299493 7890838449312224729493655)
        ·
          refine ⟨11836257673968337094240483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7890838449312224729493655 11836257673968337094240483)
          ·
            refine ⟨17754386510952505641360725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11836257673968337094240483 17754386510952505641360725)
            ·
              refine ⟨26007402115653084435587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 17754386510952505641360725 26007402115653084435587)
              ·
                rfl

theorem cell23_4102588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 11].length) (baseStart_4102588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4102588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4102588 prefixEnd_4102588 := by exact prefixLift 4102588
  have htrace : WordTrace (prefixWord ++ tailWord_4102588) baseStart_4102588 baseEnd_4102588 := by
    simpa [prefixWord, tailWord_4102588, baseEnd_4102588] using wordTrace_append hprefix tailTrace_4102588
  have hstable : (prefixWord ++ tailWord_4102588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102588).length < 2 ^ (prefixWord ++ tailWord_4102588).sum := by decide
  have hdescent : baseEnd_4102588 < baseStart_4102588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102593 : List Nat := [1, 2, 7, 1, 1, 2, 1, 1, 3, 1, 3]
def baseStart_4102593 : Nat := 118140960795 + 4102593 * 2 ^ 59
def prefixEnd_4102593 : Nat := 4983230072969 + 3 ^ 40 * 4102593 * 2
def baseEnd_4102593 : Nat := 2106602138771172319720025

theorem tailTrace_4102593 : CollatzResearch.WordTrace tailWord_4102593 prefixEnd_4102593 2106602138771172319720025 := by
  unfold tailWord_4102593
  simp only [CollatzResearch.WordTrace]
  refine ⟨149633859626013702946552433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99755906417342468631034955 149633859626013702946552433)
  ·
    refine ⟨112225394719510277209914325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149633859626013702946552433 112225394719510277209914325)
    ·
      refine ⟨2630282688738522122107367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 112225394719510277209914325 2630282688738522122107367)
      ·
        refine ⟨3945424033107783183161051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2630282688738522122107367 3945424033107783183161051)
        ·
          refine ⟨5918136049661674774741577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3945424033107783183161051 5918136049661674774741577)
          ·
            refine ⟨4438602037246256081056183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5918136049661674774741577 4438602037246256081056183)
            ·
              refine ⟨6657903055869384121584275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4438602037246256081056183 6657903055869384121584275)
              ·
                refine ⟨9986854583804076182376413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6657903055869384121584275 9986854583804076182376413)
                ·
                  refine ⟨3745070468926528568391155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9986854583804076182376413 3745070468926528568391155)
                  ·
                    refine ⟨5617605703389792852586733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3745070468926528568391155 5617605703389792852586733)
                    ·
                      refine ⟨2106602138771172319720025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5617605703389792852586733 2106602138771172319720025)
                      ·
                        rfl

theorem cell23_4102593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_4102593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4102593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4102593 prefixEnd_4102593 := by exact prefixLift 4102593
  have htrace : WordTrace (prefixWord ++ tailWord_4102593) baseStart_4102593 baseEnd_4102593 := by
    simpa [prefixWord, tailWord_4102593, baseEnd_4102593] using wordTrace_append hprefix tailTrace_4102593
  have hstable : (prefixWord ++ tailWord_4102593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102593).length < 2 ^ (prefixWord ++ tailWord_4102593).sum := by decide
  have hdescent : baseEnd_4102593 < baseStart_4102593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102599 : List Nat := [1, 1, 4, 1, 1, 6, 1, 1, 3, 2, 2]
def baseStart_4102599 : Nat := 118140960795 + 4102599 * 2 ^ 59
def prefixEnd_4102599 : Nat := 4983230072969 + 3 ^ 40 * 4102599 * 2
def baseEnd_4102599 : Nat := 2106605219655099296244997

theorem tailTrace_4102599 : CollatzResearch.WordTrace tailWord_4102599 prefixEnd_4102599 2106605219655099296244997 := by
  unfold tailWord_4102599
  simp only [CollatzResearch.WordTrace]
  refine ⟨149634078463991965971270851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99756052309327977314180567 149634078463991965971270851)
  ·
    refine ⟨224451117695987948956906277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149634078463991965971270851 224451117695987948956906277)
    ·
      refine ⟨42084584567997740429419927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 224451117695987948956906277 42084584567997740429419927)
      ·
        refine ⟨63126876851996610644129891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42084584567997740429419927 63126876851996610644129891)
        ·
          refine ⟨94690315277994915966194837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63126876851996610644129891 94690315277994915966194837)
          ·
            refine ⟨4438608528656011685915383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 94690315277994915966194837 4438608528656011685915383)
            ·
              refine ⟨6657912792984017528873075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4438608528656011685915383 6657912792984017528873075)
              ·
                refine ⟨9986869189476026293309613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6657912792984017528873075 9986869189476026293309613)
                ·
                  refine ⟨3745075946053509859991105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9986869189476026293309613 3745075946053509859991105)
                  ·
                    refine ⟨2808806959540132394993329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3745075946053509859991105 2808806959540132394993329)
                    ·
                      refine ⟨2106605219655099296244997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2808806959540132394993329 2106605219655099296244997)
                      ·
                        rfl

theorem cell23_4102599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 1, 3, 2, 2].length) (baseStart_4102599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4102599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4102599 prefixEnd_4102599 := by exact prefixLift 4102599
  have htrace : WordTrace (prefixWord ++ tailWord_4102599) baseStart_4102599 baseEnd_4102599 := by
    simpa [prefixWord, tailWord_4102599, baseEnd_4102599] using wordTrace_append hprefix tailTrace_4102599
  have hstable : (prefixWord ++ tailWord_4102599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102599).length < 2 ^ (prefixWord ++ tailWord_4102599).sum := by decide
  have hdescent : baseEnd_4102599 < baseStart_4102599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102648 : List Nat := [2, 1, 2, 1, 1, 4, 2, 2, 2, 6]
def baseStart_4102648 : Nat := 118140960795 + 4102648 * 2 ^ 59
def prefixEnd_4102648 : Nat := 4983230072969 + 3 ^ 40 * 4102648 * 2
def baseEnd_4102648 : Nat := 702210126735723201510757

theorem tailTrace_4102648 : CollatzResearch.WordTrace tailWord_4102648 prefixEnd_4102648 702210126735723201510757 := by
  unfold tailWord_4102648
  simp only [CollatzResearch.WordTrace]
  refine ⟨74817932820407223669902299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99757243760542964893203065 74817932820407223669902299)
  ·
    refine ⟨112226899230610835504853449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74817932820407223669902299 112226899230610835504853449)
    ·
      refine ⟨84170174422958126628640087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112226899230610835504853449 84170174422958126628640087)
      ·
        refine ⟨126255261634437189942960131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84170174422958126628640087 126255261634437189942960131)
        ·
          refine ⟨189382892451655784914440197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126255261634437189942960131 189382892451655784914440197)
          ·
            refine ⟨35509292334685459671457537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 189382892451655784914440197 35509292334685459671457537)
            ·
              refine ⟨26631969251014094753593153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35509292334685459671457537 26631969251014094753593153)
              ·
                refine ⟨19973976938260571065194865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26631969251014094753593153 19973976938260571065194865)
                ·
                  refine ⟨14980482703695428298896149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19973976938260571065194865 14980482703695428298896149)
                  ·
                    refine ⟨702210126735723201510757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14980482703695428298896149 702210126735723201510757)
                    ·
                      rfl

theorem cell23_4102648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 2, 6].length) (baseStart_4102648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4102648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4102648 prefixEnd_4102648 := by exact prefixLift 4102648
  have htrace : WordTrace (prefixWord ++ tailWord_4102648) baseStart_4102648 baseEnd_4102648 := by
    simpa [prefixWord, tailWord_4102648, baseEnd_4102648] using wordTrace_append hprefix tailTrace_4102648
  have hstable : (prefixWord ++ tailWord_4102648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102648).length < 2 ^ (prefixWord ++ tailWord_4102648).sum := by decide
  have hdescent : baseEnd_4102648 < baseStart_4102648 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102655 : List Nat := [1, 1, 2, 2, 1, 2, 3, 2, 3, 4, 2]
def baseStart_4102655 : Nat := 118140960795 + 4102655 * 2 ^ 59
def prefixEnd_4102655 : Nat := 4983230072969 + 3 ^ 40 * 4102655 * 2
def baseEnd_4102655 : Nat := 2106633974571751077144739

theorem tailTrace_4102655 : CollatzResearch.WordTrace tailWord_4102655 prefixEnd_4102655 2106633974571751077144739 := by
  unfold tailWord_4102655
  simp only [CollatzResearch.WordTrace]
  refine ⟨149636120951789087535309419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99757413967859391690206279 149636120951789087535309419)
  ·
    refine ⟨224454181427683631302964129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149636120951789087535309419 224454181427683631302964129)
    ·
      refine ⟨168340636070762723477223097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224454181427683631302964129 168340636070762723477223097)
      ·
        refine ⟨126255477053072042607917323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168340636070762723477223097 126255477053072042607917323)
        ·
          refine ⟨189383215579608063911875985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126255477053072042607917323 189383215579608063911875985)
          ·
            refine ⟨142037411684706047933906989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189383215579608063911875985 142037411684706047933906989)
            ·
              refine ⟨53264029381764767975215121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142037411684706047933906989 53264029381764767975215121)
              ·
                refine ⟨39948022036323575981411341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53264029381764767975215121 39948022036323575981411341)
                ·
                  refine ⟨14980508263621340993029253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39948022036323575981411341 14980508263621340993029253)
                  ·
                    refine ⟨2808845299429001436192985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14980508263621340993029253 2808845299429001436192985)
                    ·
                      refine ⟨2106633974571751077144739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2808845299429001436192985 2106633974571751077144739)
                      ·
                        rfl

theorem cell23_4102655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 3, 4, 2].length) (baseStart_4102655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4102655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4102655 prefixEnd_4102655 := by exact prefixLift 4102655
  have htrace : WordTrace (prefixWord ++ tailWord_4102655) baseStart_4102655 baseEnd_4102655 := by
    simpa [prefixWord, tailWord_4102655, baseEnd_4102655] using wordTrace_append hprefix tailTrace_4102655
  have hstable : (prefixWord ++ tailWord_4102655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102655).length < 2 ^ (prefixWord ++ tailWord_4102655).sum := by decide
  have hdescent : baseEnd_4102655 < baseStart_4102655 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102705 : List Nat := [1, 2, 2, 3, 1, 1, 3, 2, 2, 3, 3]
def baseStart_4102705 : Nat := 118140960795 + 4102705 * 2 ^ 59
def prefixEnd_4102705 : Nat := 4983230072969 + 3 ^ 40 * 4102705 * 2
def baseEnd_4102705 : Nat := 2106659648604475881519509

theorem tailTrace_4102705 : CollatzResearch.WordTrace tailWord_4102705 prefixEnd_4102705 2106659648604475881519509 := by
  unfold tailWord_4102705
  simp only [CollatzResearch.WordTrace]
  refine ⟨149637944601607946074629569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99758629734405297383086379 149637944601607946074629569)
  ·
    refine ⟨112228458451205959555972177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149637944601607946074629569 112228458451205959555972177)
    ·
      refine ⟨84171343838404469666979133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112228458451205959555972177 84171343838404469666979133)
      ·
        refine ⟨31564253939401676125117175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84171343838404469666979133 31564253939401676125117175)
        ·
          refine ⟨47346380909102514187675763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31564253939401676125117175 47346380909102514187675763)
          ·
            refine ⟨71019571363653771281513645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47346380909102514187675763 71019571363653771281513645)
            ·
              refine ⟨26632339261370164230567617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71019571363653771281513645 26632339261370164230567617)
              ·
                refine ⟨19974254446027623172925713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26632339261370164230567617 19974254446027623172925713)
                ·
                  refine ⟨14980690834520717379694285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19974254446027623172925713 14980690834520717379694285)
                  ·
                    refine ⟨5617759062945269017385357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14980690834520717379694285 5617759062945269017385357)
                    ·
                      refine ⟨2106659648604475881519509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5617759062945269017385357 2106659648604475881519509)
                      ·
                        rfl

theorem cell23_4102705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 2, 3, 3].length) (baseStart_4102705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4102705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4102705 prefixEnd_4102705 := by exact prefixLift 4102705
  have htrace : WordTrace (prefixWord ++ tailWord_4102705) baseStart_4102705 baseEnd_4102705 := by
    simpa [prefixWord, tailWord_4102705, baseEnd_4102705] using wordTrace_append hprefix tailTrace_4102705
  have hstable : (prefixWord ++ tailWord_4102705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102705).length < 2 ^ (prefixWord ++ tailWord_4102705).sum := by decide
  have hdescent : baseEnd_4102705 < baseStart_4102705 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102715 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 6, 5, 2]
def baseStart_4102715 : Nat := 118140960795 + 4102715 * 2 ^ 59
def prefixEnd_4102715 : Nat := 4983230072969 + 3 ^ 40 * 4102715 * 2
def baseEnd_4102715 : Nat := 2106664783411020842394463

theorem tailTrace_4102715 : CollatzResearch.WordTrace tailWord_4102715 prefixEnd_4102715 2106664783411020842394463 := by
  unfold tailWord_4102715
  simp only [CollatzResearch.WordTrace]
  refine ⟨149638309331571717782493599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99758872887714478521662399 149638309331571717782493599)
  ·
    refine ⟨224457463997357576673740399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149638309331571717782493599 224457463997357576673740399)
    ·
      refine ⟨336686195996036365010610599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224457463997357576673740399 336686195996036365010610599)
      ·
        refine ⟨505029293994054547515915899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336686195996036365010610599 505029293994054547515915899)
        ·
          refine ⟨757543940991081821273873849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 505029293994054547515915899 757543940991081821273873849)
          ·
            refine ⟨568157955743311365955405387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 757543940991081821273873849 568157955743311365955405387)
            ·
              refine ⟨852236933614967048933108081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 568157955743311365955405387 852236933614967048933108081)
              ·
                refine ⟨639177700211225286699831061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 852236933614967048933108081 639177700211225286699831061)
                ·
                  refine ⟨29961454697401185314054581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 639177700211225286699831061 29961454697401185314054581)
                  ·
                    refine ⟨2808886377881361123192617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29961454697401185314054581 2808886377881361123192617)
                    ·
                      refine ⟨2106664783411020842394463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2808886377881361123192617 2106664783411020842394463)
                      ·
                        rfl

theorem cell23_4102715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 5, 2].length) (baseStart_4102715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4102715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4102715 prefixEnd_4102715 := by exact prefixLift 4102715
  have htrace : WordTrace (prefixWord ++ tailWord_4102715) baseStart_4102715 baseEnd_4102715 := by
    simpa [prefixWord, tailWord_4102715, baseEnd_4102715] using wordTrace_append hprefix tailTrace_4102715
  have hstable : (prefixWord ++ tailWord_4102715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102715).length < 2 ^ (prefixWord ++ tailWord_4102715).sum := by decide
  have hdescent : baseEnd_4102715 < baseStart_4102715 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102762 : List Nat := [3, 1, 3, 2, 1, 1, 3, 2, 2, 1, 4]
def baseStart_4102762 : Nat := 118140960795 + 4102762 * 2 ^ 59
def prefixEnd_4102762 : Nat := 4983230072969 + 3 ^ 40 * 4102762 * 2
def baseEnd_4102762 : Nat := 2106688917001782158506747

theorem tailTrace_4102762 : CollatzResearch.WordTrace tailWord_4102762 prefixEnd_4102762 2106688917001782158506747 := by
  unfold tailWord_4102762
  simp only [CollatzResearch.WordTrace]
  refine ⟨37410005890600361202363635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99760015708267629872969693 37410005890600361202363635)
  ·
    refine ⟨56115008835900541803545453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37410005890600361202363635 56115008835900541803545453)
    ·
      refine ⟨21043128313462703176329545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56115008835900541803545453 21043128313462703176329545)
      ·
        refine ⟨15782346235097027382247159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21043128313462703176329545 15782346235097027382247159)
        ·
          refine ⟨23673519352645541073370739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15782346235097027382247159 23673519352645541073370739)
          ·
            refine ⟨35510279028968311610056109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23673519352645541073370739 35510279028968311610056109)
            ·
              refine ⟨13316354635863116853771041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35510279028968311610056109 13316354635863116853771041)
              ·
                refine ⟨9987265976897337640328281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13316354635863116853771041 9987265976897337640328281)
                ·
                  refine ⟨7490449482673003230246211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9987265976897337640328281 7490449482673003230246211)
                  ·
                    refine ⟨11235674224009504845369317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7490449482673003230246211 11235674224009504845369317)
                    ·
                      refine ⟨2106688917001782158506747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11235674224009504845369317 2106688917001782158506747)
                      ·
                        rfl

theorem cell23_4102762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_4102762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4102762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4102762 prefixEnd_4102762 := by exact prefixLift 4102762
  have htrace : WordTrace (prefixWord ++ tailWord_4102762) baseStart_4102762 baseEnd_4102762 := by
    simpa [prefixWord, tailWord_4102762, baseEnd_4102762] using wordTrace_append hprefix tailTrace_4102762
  have hstable : (prefixWord ++ tailWord_4102762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102762).length < 2 ^ (prefixWord ++ tailWord_4102762).sum := by decide
  have hdescent : baseEnd_4102762 < baseStart_4102762 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102823 : List Nat := [1, 1, 6, 3, 1, 1, 1, 4, 1, 4]
def baseStart_4102823 : Nat := 118140960795 + 4102823 * 2 ^ 59
def prefixEnd_4102823 : Nat := 4983230072969 + 3 ^ 40 * 4102823 * 2
def baseEnd_4102823 : Nat := 702240079773902139947989

theorem tailTrace_4102823 : CollatzResearch.WordTrace tailWord_4102823 prefixEnd_4102823 702240079773902139947989 := by
  unfold tailWord_4102823
  simp only [CollatzResearch.WordTrace]
  refine ⟨149642248415180452227425123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99761498943453634818283415 149642248415180452227425123)
  ·
    refine ⟨224463372622770678341137685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149642248415180452227425123 224463372622770678341137685)
    ·
      refine ⟨10521720591692375547240829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 224463372622770678341137685 10521720591692375547240829)
      ·
        refine ⟨3945645221884640830215311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10521720591692375547240829 3945645221884640830215311)
        ·
          refine ⟨5918467832826961245322967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3945645221884640830215311 5918467832826961245322967)
          ·
            refine ⟨8877701749240441867984451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5918467832826961245322967 8877701749240441867984451)
            ·
              refine ⟨13316552623860662801976677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8877701749240441867984451 13316552623860662801976677)
              ·
                refine ⟨2496853616973874275370627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13316552623860662801976677 2496853616973874275370627)
                ·
                  refine ⟨3745280425460811413055941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2496853616973874275370627 3745280425460811413055941)
                  ·
                    refine ⟨702240079773902139947989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3745280425460811413055941 702240079773902139947989)
                    ·
                      rfl

theorem cell23_4102823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_4102823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4102823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4102823 prefixEnd_4102823 := by exact prefixLift 4102823
  have htrace : WordTrace (prefixWord ++ tailWord_4102823) baseStart_4102823 baseEnd_4102823 := by
    simpa [prefixWord, tailWord_4102823, baseEnd_4102823] using wordTrace_append hprefix tailTrace_4102823
  have hstable : (prefixWord ++ tailWord_4102823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102823).length < 2 ^ (prefixWord ++ tailWord_4102823).sum := by decide
  have hdescent : baseEnd_4102823 < baseStart_4102823 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102855 : List Nat := [1, 1, 4, 1, 1, 1, 2, 1, 5, 1, 5]
def baseStart_4102855 : Nat := 118140960795 + 4102855 * 2 ^ 59
def prefixEnd_4102855 : Nat := 4983230072969 + 3 ^ 40 * 4102855 * 2
def baseEnd_4102855 : Nat := 2106736670702650294643819

theorem tailTrace_4102855 : CollatzResearch.WordTrace tailWord_4102855 prefixEnd_4102855 2106736670702650294643819 := by
  unfold tailWord_4102855
  simp only [CollatzResearch.WordTrace]
  refine ⟨149643415551064521692590019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99762277034043014461726679 149643415551064521692590019)
  ·
    refine ⟨224465123326596782538885029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149643415551064521692590019 224465123326596782538885029)
    ·
      refine ⟨42087210623736896726040943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 224465123326596782538885029 42087210623736896726040943)
      ·
        refine ⟨63130815935605345089061415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42087210623736896726040943 63130815935605345089061415)
        ·
          refine ⟨94696223903408017633592123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63130815935605345089061415 94696223903408017633592123)
          ·
            refine ⟨142044335855112026450388185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94696223903408017633592123 142044335855112026450388185)
            ·
              refine ⟨106533251891334019837791139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142044335855112026450388185 106533251891334019837791139)
              ·
                refine ⟨159799877837001029756686709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106533251891334019837791139 159799877837001029756686709)
                ·
                  refine ⟨14981238547218846539689379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 159799877837001029756686709 14981238547218846539689379)
                  ·
                    refine ⟨22471857820828269809534069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14981238547218846539689379 22471857820828269809534069)
                    ·
                      refine ⟨2106736670702650294643819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22471857820828269809534069 2106736670702650294643819)
                      ·
                        rfl

theorem cell23_4102855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 5, 1, 5].length) (baseStart_4102855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4102855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4102855 prefixEnd_4102855 := by exact prefixLift 4102855
  have htrace : WordTrace (prefixWord ++ tailWord_4102855) baseStart_4102855 baseEnd_4102855 := by
    simpa [prefixWord, tailWord_4102855, baseEnd_4102855] using wordTrace_append hprefix tailTrace_4102855
  have hstable : (prefixWord ++ tailWord_4102855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102855).length < 2 ^ (prefixWord ++ tailWord_4102855).sum := by decide
  have hdescent : baseEnd_4102855 < baseStart_4102855 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102856 : List Nat := [2, 1, 3, 1, 2, 5, 1, 1, 2, 3, 2]
def baseStart_4102856 : Nat := 118140960795 + 4102856 * 2 ^ 59
def prefixEnd_4102856 : Nat := 4983230072969 + 3 ^ 40 * 4102856 * 2
def baseEnd_4102856 : Nat := 2106737184183304790731315

theorem tailTrace_4102856 : CollatzResearch.WordTrace tailWord_4102856 prefixEnd_4102856 2106737184183304790731315 := by
  unfold tailWord_4102856
  simp only [CollatzResearch.WordTrace]
  refine ⟨74821726012030449431688211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99762301349373932575584281 74821726012030449431688211)
  ·
    refine ⟨112232589018045674147532317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74821726012030449431688211 112232589018045674147532317)
    ·
      refine ⟨42087220881767127805324619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112232589018045674147532317 42087220881767127805324619)
      ·
        refine ⟨63130831322650691707986929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42087220881767127805324619 63130831322650691707986929)
        ·
          refine ⟨47348123491988018780990197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63130831322650691707986929 47348123491988018780990197)
          ·
            refine ⟨4438886577373876760717831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47348123491988018780990197 4438886577373876760717831)
            ·
              refine ⟨6658329866060815141076747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4438886577373876760717831 6658329866060815141076747)
              ·
                refine ⟨9987494799091222711615121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6658329866060815141076747 9987494799091222711615121)
                ·
                  refine ⟨7490621099318417033711341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9987494799091222711615121 7490621099318417033711341)
                  ·
                    refine ⟨2808982912244406387641753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7490621099318417033711341 2808982912244406387641753)
                    ·
                      refine ⟨2106737184183304790731315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2808982912244406387641753 2106737184183304790731315)
                      ·
                        rfl

theorem cell23_4102856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 1, 2, 3, 2].length) (baseStart_4102856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4102856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4102856 prefixEnd_4102856 := by exact prefixLift 4102856
  have htrace : WordTrace (prefixWord ++ tailWord_4102856) baseStart_4102856 baseEnd_4102856 := by
    simpa [prefixWord, tailWord_4102856, baseEnd_4102856] using wordTrace_append hprefix tailTrace_4102856
  have hstable : (prefixWord ++ tailWord_4102856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102856).length < 2 ^ (prefixWord ++ tailWord_4102856).sum := by decide
  have hdescent : baseEnd_4102856 < baseStart_4102856 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102862 : List Nat := [4, 1, 1, 1, 3, 2, 2, 2, 1, 6]
def baseStart_4102862 : Nat := 118140960795 + 4102862 * 2 ^ 59
def prefixEnd_4102862 : Nat := 4983230072969 + 3 ^ 40 * 4102862 * 2
def baseEnd_4102862 : Nat := 702246755022410589085429

theorem tailTrace_4102862 : CollatzResearch.WordTrace tailWord_4102862 prefixEnd_4102862 702246755022410589085429 := by
  unfold tailWord_4102862
  simp only [CollatzResearch.WordTrace]
  refine ⟨18705458857754895236011855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99762447241359441258729893 18705458857754895236011855)
  ·
    refine ⟨28058188286632342854017783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18705458857754895236011855 28058188286632342854017783)
    ·
      refine ⟨42087282429948514281026675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28058188286632342854017783 42087282429948514281026675)
      ·
        refine ⟨63130923644922771421540013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42087282429948514281026675 63130923644922771421540013)
        ·
          refine ⟨23674096366846039283077505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63130923644922771421540013 23674096366846039283077505)
          ·
            refine ⟨17755572275134529462308129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23674096366846039283077505 17755572275134529462308129)
            ·
              refine ⟨13316679206350897096731097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17755572275134529462308129 13316679206350897096731097)
              ·
                refine ⟨9987509404763172822548323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13316679206350897096731097 9987509404763172822548323)
                ·
                  refine ⟨14981264107144759233822485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9987509404763172822548323 14981264107144759233822485)
                  ·
                    refine ⟨702246755022410589085429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14981264107144759233822485 702246755022410589085429)
                    ·
                      rfl

theorem cell23_4102862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 2, 1, 6].length) (baseStart_4102862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4102862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4102862 prefixEnd_4102862 := by exact prefixLift 4102862
  have htrace : WordTrace (prefixWord ++ tailWord_4102862) baseStart_4102862 baseEnd_4102862 := by
    simpa [prefixWord, tailWord_4102862, baseEnd_4102862] using wordTrace_append hprefix tailTrace_4102862
  have hstable : (prefixWord ++ tailWord_4102862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102862).length < 2 ^ (prefixWord ++ tailWord_4102862).sum := by decide
  have hdescent : baseEnd_4102862 < baseStart_4102862 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102879 : List Nat := [1, 1, 2, 3, 2, 3, 3, 2, 2, 4]
def baseStart_4102879 : Nat := 118140960795 + 4102879 * 2 ^ 59
def prefixEnd_4102879 : Nat := 4983230072969 + 3 ^ 40 * 4102879 * 2
def baseEnd_4102879 : Nat := 702249664746119400247903

theorem tailTrace_4102879 : CollatzResearch.WordTrace tailWord_4102879 prefixEnd_4102879 702249664746119400247903 := by
  unfold tailWord_4102879
  simp only [CollatzResearch.WordTrace]
  refine ⟨149644290902977573791463691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99762860601985049194309127 149644290902977573791463691)
  ·
    refine ⟨224466436354466360687195537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149644290902977573791463691 224466436354466360687195537)
    ·
      refine ⟨168349827265849770515396653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224466436354466360687195537 168349827265849770515396653)
      ·
        refine ⟨63131185224693663943273745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168349827265849770515396653 63131185224693663943273745)
        ·
          refine ⟨47348388918520247957455309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63131185224693663943273745 47348388918520247957455309)
          ·
            refine ⟨17755645844445092984045741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47348388918520247957455309 17755645844445092984045741)
            ·
              refine ⟨6658367191666909869017153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17755645844445092984045741 6658367191666909869017153)
              ·
                refine ⟨4993775393750182401762865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6658367191666909869017153 4993775393750182401762865)
                ·
                  refine ⟨3745331545312636801322149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4993775393750182401762865 3745331545312636801322149)
                  ·
                    refine ⟨702249664746119400247903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3745331545312636801322149 702249664746119400247903)
                    ·
                      rfl

theorem cell23_4102879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 2, 2, 4].length) (baseStart_4102879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4102879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4102879 prefixEnd_4102879 := by exact prefixLift 4102879
  have htrace : WordTrace (prefixWord ++ tailWord_4102879) baseStart_4102879 baseEnd_4102879 := by
    simpa [prefixWord, tailWord_4102879, baseEnd_4102879] using wordTrace_append hprefix tailTrace_4102879
  have hstable : (prefixWord ++ tailWord_4102879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102879).length < 2 ^ (prefixWord ++ tailWord_4102879).sum := by decide
  have hdescent : baseEnd_4102879 < baseStart_4102879 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102905 : List Nat := [1, 2, 1, 3, 1, 1, 1, 4, 2, 7]
def baseStart_4102905 : Nat := 118140960795 + 4102905 * 2 ^ 59
def prefixEnd_4102905 : Nat := 4983230072969 + 3 ^ 40 * 4102905 * 2
def baseEnd_4102905 : Nat := 702254114911791699672863

theorem tailTrace_4102905 : CollatzResearch.WordTrace tailWord_4102905 prefixEnd_4102905 702254114911791699672863 := by
  unfold tailWord_4102905
  simp only [CollatzResearch.WordTrace]
  refine ⟨149645239200883380231910169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99763492800588920154606779 149645239200883380231910169)
  ·
    refine ⟨112233929400662535173932627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149645239200883380231910169 112233929400662535173932627)
    ·
      refine ⟨168350894100993802760898941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112233929400662535173932627 168350894100993802760898941)
      ·
        refine ⟨63131585287872676035337103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168350894100993802760898941 63131585287872676035337103)
        ·
          refine ⟨94697377931809014053005655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63131585287872676035337103 94697377931809014053005655)
          ·
            refine ⟨142046066897713521079508483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94697377931809014053005655 142046066897713521079508483)
            ·
              refine ⟨213069100346570281619262725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142046066897713521079508483 213069100346570281619262725)
              ·
                refine ⟨39950456314981927803611761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 213069100346570281619262725 39950456314981927803611761)
                ·
                  refine ⟨29962842236236445852708821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39950456314981927803611761 29962842236236445852708821)
                  ·
                    refine ⟨702254114911791699672863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29962842236236445852708821 702254114911791699672863)
                    ·
                      rfl

theorem cell23_4102905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 7].length) (baseStart_4102905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4102905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4102905 prefixEnd_4102905 := by exact prefixLift 4102905
  have htrace : WordTrace (prefixWord ++ tailWord_4102905) baseStart_4102905 baseEnd_4102905 := by
    simpa [prefixWord, tailWord_4102905, baseEnd_4102905] using wordTrace_append hprefix tailTrace_4102905
  have hstable : (prefixWord ++ tailWord_4102905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102905).length < 2 ^ (prefixWord ++ tailWord_4102905).sum := by decide
  have hdescent : baseEnd_4102905 < baseStart_4102905 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102920 : List Nat := [2, 1, 3, 2, 2, 4, 1, 3, 1, 2, 2]
def baseStart_4102920 : Nat := 118140960795 + 4102920 * 2 ^ 59
def prefixEnd_4102920 : Nat := 4983230072969 + 3 ^ 40 * 4102920 * 2
def baseEnd_4102920 : Nat := 2106770046945192540331021

theorem tailTrace_4102920 : CollatzResearch.WordTrace tailWord_4102920 prefixEnd_4102920 2106770046945192540331021 := by
  unfold tailWord_4102920
  simp only [CollatzResearch.WordTrace]
  refine ⟨74822893147914518896853107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99763857530552691862470809 74822893147914518896853107)
  ·
    refine ⟨112234339721871778345279661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74822893147914518896853107 112234339721871778345279661)
    ·
      refine ⟨42087877395701916879479873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112234339721871778345279661 42087877395701916879479873)
      ·
        refine ⟨31565908046776437659609905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42087877395701916879479873 31565908046776437659609905)
        ·
          refine ⟨23674431035082328244707429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31565908046776437659609905 23674431035082328244707429)
          ·
            refine ⟨4438955819077936545882643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23674431035082328244707429 4438955819077936545882643)
            ·
              refine ⟨6658433728616904818823965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4438955819077936545882643 6658433728616904818823965)
              ·
                refine ⟨2496912648231339307058987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6658433728616904818823965 2496912648231339307058987)
                ·
                  refine ⟨3745368972347008960588481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2496912648231339307058987 3745368972347008960588481)
                  ·
                    refine ⟨2809026729260256720441361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3745368972347008960588481 2809026729260256720441361)
                    ·
                      refine ⟨2106770046945192540331021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2809026729260256720441361 2106770046945192540331021)
                      ·
                        rfl

theorem cell23_4102920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 3, 1, 2, 2].length) (baseStart_4102920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4102920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4102920 prefixEnd_4102920 := by exact prefixLift 4102920
  have htrace : WordTrace (prefixWord ++ tailWord_4102920) baseStart_4102920 baseEnd_4102920 := by
    simpa [prefixWord, tailWord_4102920, baseEnd_4102920] using wordTrace_append hprefix tailTrace_4102920
  have hstable : (prefixWord ++ tailWord_4102920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102920).length < 2 ^ (prefixWord ++ tailWord_4102920).sum := by decide
  have hdescent : baseEnd_4102920 < baseStart_4102920 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102952 : List Nat := [2, 1, 5, 1, 1, 1, 2, 1, 1, 8]
def baseStart_4102952 : Nat := 118140960795 + 4102952 * 2 ^ 59
def prefixEnd_4102952 : Nat := 4983230072969 + 3 ^ 40 * 4102952 * 2
def baseEnd_4102952 : Nat := 702262159442045471710291

theorem tailTrace_4102952 : CollatzResearch.WordTrace tailWord_4102952 prefixEnd_4102952 702262159442045471710291 := by
  unfold tailWord_4102952
  simp only [CollatzResearch.WordTrace]
  refine ⟨74823476715856553629435555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99764635621142071505914073 74823476715856553629435555)
  ·
    refine ⟨112235215073784830444153333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74823476715856553629435555 112235215073784830444153333)
    ·
      refine ⟨10522051413167327854139375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 112235215073784830444153333 10522051413167327854139375)
      ·
        refine ⟨15783077119750991781209063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10522051413167327854139375 15783077119750991781209063)
        ·
          refine ⟨23674615679626487671813595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15783077119750991781209063 23674615679626487671813595)
          ·
            refine ⟨35511923519439731507720393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23674615679626487671813595 35511923519439731507720393)
            ·
              refine ⟨26633942639579798630790295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35511923519439731507720393 26633942639579798630790295)
              ·
                refine ⟨39950913959369697946185443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26633942639579798630790295 39950913959369697946185443)
                ·
                  refine ⟨59926370939054546919278165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39950913959369697946185443 59926370939054546919278165)
                  ·
                    refine ⟨702262159442045471710291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 59926370939054546919278165 702262159442045471710291)
                    ·
                      rfl

theorem cell23_4102952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_4102952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4102952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4102952 prefixEnd_4102952 := by exact prefixLift 4102952
  have htrace : WordTrace (prefixWord ++ tailWord_4102952) baseStart_4102952 baseEnd_4102952 := by
    simpa [prefixWord, tailWord_4102952, baseEnd_4102952] using wordTrace_append hprefix tailTrace_4102952
  have hstable : (prefixWord ++ tailWord_4102952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102952).length < 2 ^ (prefixWord ++ tailWord_4102952).sum := by decide
  have hdescent : baseEnd_4102952 < baseStart_4102952 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102957 : List Nat := [1, 5, 3, 2, 2, 1, 1, 2, 1, 2, 3]
def baseStart_4102957 : Nat := 118140960795 + 4102957 * 2 ^ 59
def prefixEnd_4102957 : Nat := 4983230072969 + 3 ^ 40 * 4102957 * 2
def baseEnd_4102957 : Nat := 2106789045729408895568351

theorem tailTrace_4102957 : CollatzResearch.WordTrace tailWord_4102957 prefixEnd_4102957 2106789045729408895568351 := by
  unfold tailWord_4102957
  simp only [CollatzResearch.WordTrace]
  refine ⟨149647135796694993112803125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99764757197796662075202083 149647135796694993112803125)
  ·
    refine ⟨14029418980940155604325293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 149647135796694993112803125 14029418980940155604325293)
    ·
      refine ⟨5261032117852558351621985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14029418980940155604325293 5261032117852558351621985)
      ·
        refine ⟨3945774088389418763716489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5261032117852558351621985 3945774088389418763716489)
        ·
          refine ⟨2959330566292064072787367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3945774088389418763716489 2959330566292064072787367)
          ·
            refine ⟨4438995849438096109181051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2959330566292064072787367 4438995849438096109181051)
            ·
              refine ⟨6658493774157144163771577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4438995849438096109181051 6658493774157144163771577)
              ·
                refine ⟨4993870330617858122828683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6658493774157144163771577 4993870330617858122828683)
                ·
                  refine ⟨7490805495926787184243025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4993870330617858122828683 7490805495926787184243025)
                  ·
                    refine ⟨5618104121945090388182269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7490805495926787184243025 5618104121945090388182269)
                    ·
                      refine ⟨2106789045729408895568351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5618104121945090388182269 2106789045729408895568351)
                      ·
                        rfl

theorem cell23_4102957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_4102957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4102957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4102957 prefixEnd_4102957 := by exact prefixLift 4102957
  have htrace : WordTrace (prefixWord ++ tailWord_4102957) baseStart_4102957 baseEnd_4102957 := by
    simpa [prefixWord, tailWord_4102957, baseEnd_4102957] using wordTrace_append hprefix tailTrace_4102957
  have hstable : (prefixWord ++ tailWord_4102957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102957).length < 2 ^ (prefixWord ++ tailWord_4102957).sum := by decide
  have hdescent : baseEnd_4102957 < baseStart_4102957 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102962 : List Nat := [3, 2, 1, 1, 3, 1, 1, 1, 4, 1, 5]
def baseStart_4102962 : Nat := 118140960795 + 4102962 * 2 ^ 59
def prefixEnd_4102962 : Nat := 4983230072969 + 3 ^ 40 * 4102962 * 2
def baseEnd_4102962 : Nat := 2106791613132681376005827

theorem tailTrace_4102962 : CollatzResearch.WordTrace tailWord_4102962 prefixEnd_4102962 2106791613132681376005827 := by
  unfold tailWord_4102962
  simp only [CollatzResearch.WordTrace]
  refine ⟨37411829540419219741683785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99764878774451252644490093 37411829540419219741683785)
  ·
    refine ⟨28058872155314414806262839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37411829540419219741683785 28058872155314414806262839)
    ·
      refine ⟨42088308232971622209394259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28058872155314414806262839 42088308232971622209394259)
      ·
        refine ⟨63132462349457433314091389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42088308232971622209394259 63132462349457433314091389)
        ·
          refine ⟨23674673381046537492784271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63132462349457433314091389 23674673381046537492784271)
          ·
            refine ⟨35512010071569806239176407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23674673381046537492784271 35512010071569806239176407)
            ·
              refine ⟨53268015107354709358764611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35512010071569806239176407 53268015107354709358764611)
              ·
                refine ⟨79902022661032064038146917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53268015107354709358764611 79902022661032064038146917)
                ·
                  refine ⟨14981629248943512007152547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79902022661032064038146917 14981629248943512007152547)
                  ·
                    refine ⟨22472443873415268010728821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14981629248943512007152547 22472443873415268010728821)
                    ·
                      refine ⟨2106791613132681376005827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22472443873415268010728821 2106791613132681376005827)
                      ·
                        rfl

theorem cell23_4102962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 4, 1, 5].length) (baseStart_4102962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4102962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4102962 prefixEnd_4102962 := by exact prefixLift 4102962
  have htrace : WordTrace (prefixWord ++ tailWord_4102962) baseStart_4102962 baseEnd_4102962 := by
    simpa [prefixWord, tailWord_4102962, baseEnd_4102962] using wordTrace_append hprefix tailTrace_4102962
  have hstable : (prefixWord ++ tailWord_4102962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102962).length < 2 ^ (prefixWord ++ tailWord_4102962).sum := by decide
  have hdescent : baseEnd_4102962 < baseStart_4102962 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102963 : List Nat := [1, 1, 1, 2, 6, 3, 1, 2, 1, 3, 2]
def baseStart_4102963 : Nat := 118140960795 + 4102963 * 2 ^ 59
def prefixEnd_4102963 : Nat := 4983230072969 + 3 ^ 40 * 4102963 * 2
def baseEnd_4102963 : Nat := 2106792126613335872093323

theorem tailTrace_4102963 : CollatzResearch.WordTrace tailWord_4102963 prefixEnd_4102963 2106792126613335872093323 := by
  unfold tailWord_4102963
  simp only [CollatzResearch.WordTrace]
  refine ⟨149647354634673256137521543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99764903089782170758347695 149647354634673256137521543)
  ·
    refine ⟨224471031952009884206282315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149647354634673256137521543 224471031952009884206282315)
    ·
      refine ⟨336706547928014826309423473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224471031952009884206282315 336706547928014826309423473)
      ·
        refine ⟨252529910946011119732067605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336706547928014826309423473 252529910946011119732067605)
        ·
          refine ⟨11837339575594271237440669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 252529910946011119732067605 11837339575594271237440669)
          ·
            refine ⟨4439002340847851714040251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11837339575594271237440669 4439002340847851714040251)
            ·
              refine ⟨6658503511271777571060377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4439002340847851714040251 6658503511271777571060377)
              ·
                refine ⟨4993877633453833178295283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6658503511271777571060377 4993877633453833178295283)
                ·
                  refine ⟨7490816450180749767442925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4993877633453833178295283 7490816450180749767442925)
                  ·
                    refine ⟨2809056168817781162791097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7490816450180749767442925 2809056168817781162791097)
                    ·
                      refine ⟨2106792126613335872093323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2809056168817781162791097 2106792126613335872093323)
                      ·
                        rfl

theorem cell23_4102963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 2, 1, 3, 2].length) (baseStart_4102963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4102963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4102963 prefixEnd_4102963 := by exact prefixLift 4102963
  have htrace : WordTrace (prefixWord ++ tailWord_4102963) baseStart_4102963 baseEnd_4102963 := by
    simpa [prefixWord, tailWord_4102963, baseEnd_4102963] using wordTrace_append hprefix tailTrace_4102963
  have hstable : (prefixWord ++ tailWord_4102963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102963).length < 2 ^ (prefixWord ++ tailWord_4102963).sum := by decide
  have hdescent : baseEnd_4102963 < baseStart_4102963 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102972 : List Nat := [2, 2, 2, 2, 1, 1, 1, 2, 4, 2, 4]
def baseStart_4102972 : Nat := 118140960795 + 4102972 * 2 ^ 59
def prefixEnd_4102972 : Nat := 4983230072969 + 3 ^ 40 * 4102972 * 2
def baseEnd_4102972 : Nat := 2106796747939226336880781

theorem tailTrace_4102972 : CollatzResearch.WordTrace tailWord_4102972 prefixEnd_4102972 2106796747939226336880781 := by
  unfold tailWord_4102972
  simp only [CollatzResearch.WordTrace]
  refine ⟨74823841445820325337299585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99765121927760433783066113 74823841445820325337299585)
  ·
    refine ⟨56117881084365244002974689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74823841445820325337299585 56117881084365244002974689)
    ·
      refine ⟨42088410813273933002231017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56117881084365244002974689 42088410813273933002231017)
      ·
        refine ⟨31566308109955449751673263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42088410813273933002231017 31566308109955449751673263)
        ·
          refine ⟨47349462164933174627509895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31566308109955449751673263 47349462164933174627509895)
          ·
            refine ⟨71024193247399761941264843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47349462164933174627509895 71024193247399761941264843)
            ·
              refine ⟨106536289871099642911897265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71024193247399761941264843 106536289871099642911897265)
              ·
                refine ⟨79902217403324732183922949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106536289871099642911897265 79902217403324732183922949)
                ·
                  refine ⟨14981665763123387284485553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79902217403324732183922949 14981665763123387284485553)
                  ·
                    refine ⟨11236249322342540463364165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14981665763123387284485553 11236249322342540463364165)
                    ·
                      refine ⟨2106796747939226336880781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11236249322342540463364165 2106796747939226336880781)
                      ·
                        rfl

theorem cell23_4102972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_4102972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4102972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4102972 prefixEnd_4102972 := by exact prefixLift 4102972
  have htrace : WordTrace (prefixWord ++ tailWord_4102972) baseStart_4102972 baseEnd_4102972 := by
    simpa [prefixWord, tailWord_4102972, baseEnd_4102972] using wordTrace_append hprefix tailTrace_4102972
  have hstable : (prefixWord ++ tailWord_4102972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102972).length < 2 ^ (prefixWord ++ tailWord_4102972).sum := by decide
  have hdescent : baseEnd_4102972 < baseStart_4102972 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103029 : List Nat := [1, 3, 4, 1, 1, 3, 1, 1, 1, 7]
def baseStart_4103029 : Nat := 118140960795 + 4103029 * 2 ^ 59
def prefixEnd_4103029 : Nat := 4983230072969 + 3 ^ 40 * 4103029 * 2
def baseEnd_4103029 : Nat := 702275338778844204622673

theorem tailTrace_4103029 : CollatzResearch.WordTrace tailWord_4103029 prefixEnd_4103029 702275338778844204622673 := by
  unfold tailWord_4103029
  simp only [CollatzResearch.WordTrace]
  refine ⟨149649761852434149409424141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99766507901622766272949427 149649761852434149409424141)
  ·
    refine ⟨56118660694662806028534053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149649761852434149409424141 56118660694662806028534053)
    ·
      refine ⟨10522248880249276130350135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56118660694662806028534053 10522248880249276130350135)
      ·
        refine ⟨15783373320373914195525203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10522248880249276130350135 15783373320373914195525203)
        ·
          refine ⟨23675059980560871293287805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15783373320373914195525203 23675059980560871293287805)
          ·
            refine ⟨8878147492710326734982927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23675059980560871293287805 8878147492710326734982927)
            ·
              refine ⟨13317221239065490102474391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8878147492710326734982927 13317221239065490102474391)
              ·
                refine ⟨19975831858598235153711587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13317221239065490102474391 19975831858598235153711587)
                ·
                  refine ⟨29963747787897352730567381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19975831858598235153711587 29963747787897352730567381)
                  ·
                    refine ⟨702275338778844204622673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29963747787897352730567381 702275338778844204622673)
                    ·
                      rfl

theorem cell23_4103029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_4103029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4103029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4103029 prefixEnd_4103029 := by exact prefixLift 4103029
  have htrace : WordTrace (prefixWord ++ tailWord_4103029) baseStart_4103029 baseEnd_4103029 := by
    simpa [prefixWord, tailWord_4103029, baseEnd_4103029] using wordTrace_append hprefix tailTrace_4103029
  have hstable : (prefixWord ++ tailWord_4103029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103029).length < 2 ^ (prefixWord ++ tailWord_4103029).sum := by decide
  have hdescent : baseEnd_4103029 < baseStart_4103029 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103052 : List Nat := [2, 2, 1, 2, 1, 2, 2, 1, 2, 3, 5]
def baseStart_4103052 : Nat := 118140960795 + 4103052 * 2 ^ 59
def prefixEnd_4103052 : Nat := 4983230072969 + 3 ^ 40 * 4103052 * 2
def baseEnd_4103052 : Nat := 2106837826391586023880413

theorem tailTrace_4103052 : CollatzResearch.WordTrace tailWord_4103052 prefixEnd_4103052 2106837826391586023880413 := by
  unfold tailWord_4103052
  simp only [CollatzResearch.WordTrace]
  refine ⟨74825300365675412168755705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99767067154233882891674273 74825300365675412168755705)
  ·
    refine ⟨56118975274256559126566779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74825300365675412168755705 56118975274256559126566779)
    ·
      refine ⟨84178462911384838689850169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56118975274256559126566779 84178462911384838689850169)
      ·
        refine ⟨63133847183538629017387627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84178462911384838689850169 63133847183538629017387627)
        ·
          refine ⟨94700770775307943526081441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63133847183538629017387627 94700770775307943526081441)
          ·
            refine ⟨71025578081480957644561081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94700770775307943526081441 71025578081480957644561081)
            ·
              refine ⟨53269183561110718233420811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71025578081480957644561081 53269183561110718233420811)
              ·
                refine ⟨79903775341666077350131217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53269183561110718233420811 79903775341666077350131217)
                ·
                  refine ⟨59927831506249558012598413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79903775341666077350131217 59927831506249558012598413)
                  ·
                    refine ⟨22472936814843584254724405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59927831506249558012598413 22472936814843584254724405)
                    ·
                      refine ⟨2106837826391586023880413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22472936814843584254724405 2106837826391586023880413)
                      ·
                        rfl

theorem cell23_4103052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_4103052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4103052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4103052 prefixEnd_4103052 := by exact prefixLift 4103052
  have htrace : WordTrace (prefixWord ++ tailWord_4103052) baseStart_4103052 baseEnd_4103052 := by
    simpa [prefixWord, tailWord_4103052, baseEnd_4103052] using wordTrace_append hprefix tailTrace_4103052
  have hstable : (prefixWord ++ tailWord_4103052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103052).length < 2 ^ (prefixWord ++ tailWord_4103052).sum := by decide
  have hdescent : baseEnd_4103052 < baseStart_4103052 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103069 : List Nat := [1, 4, 2, 1, 2, 1, 1, 1, 3, 4, 3]
def baseStart_4103069 : Nat := 118140960795 + 4103069 * 2 ^ 59
def prefixEnd_4103069 : Nat := 4983230072969 + 3 ^ 40 * 4103069 * 2
def baseEnd_4103069 : Nat := 2106846555562712457367835

theorem tailTrace_4103069 : CollatzResearch.WordTrace tailWord_4103069 prefixEnd_4103069 2106846555562712457367835 := by
  unfold tailWord_4103069
  simp only [CollatzResearch.WordTrace]
  refine ⟨149651220772289236240880261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99767480514859490827253507 149651220772289236240880261)
  ·
    refine ⟨28059603894804231795165049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149651220772289236240880261 28059603894804231795165049)
    ·
      refine ⟨21044702921103173846373787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28059603894804231795165049 21044702921103173846373787)
      ·
        refine ⟨31567054381654760769560681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21044702921103173846373787 31567054381654760769560681)
        ·
          refine ⟨23675290786241070577170511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31567054381654760769560681 23675290786241070577170511)
          ·
            refine ⟨35512936179361605865755767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23675290786241070577170511 35512936179361605865755767)
            ·
              refine ⟨53269404269042408798633651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35512936179361605865755767 53269404269042408798633651)
              ·
                refine ⟨79904106403563613197950477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53269404269042408798633651 79904106403563613197950477)
                ·
                  refine ⟨29964039901336354949231429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79904106403563613197950477 29964039901336354949231429)
                  ·
                    refine ⟨5618257481500566552980893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29964039901336354949231429 5618257481500566552980893)
                    ·
                      refine ⟨2106846555562712457367835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5618257481500566552980893 2106846555562712457367835)
                      ·
                        rfl

theorem cell23_4103069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 4, 3].length) (baseStart_4103069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4103069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4103069 prefixEnd_4103069 := by exact prefixLift 4103069
  have htrace : WordTrace (prefixWord ++ tailWord_4103069) baseStart_4103069 baseEnd_4103069 := by
    simpa [prefixWord, tailWord_4103069, baseEnd_4103069] using wordTrace_append hprefix tailTrace_4103069
  have hstable : (prefixWord ++ tailWord_4103069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103069).length < 2 ^ (prefixWord ++ tailWord_4103069).sum := by decide
  have hdescent : baseEnd_4103069 < baseStart_4103069 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103143 : List Nat := [1, 1, 5, 2, 2, 1, 1, 3, 2, 3, 2]
def baseStart_4103143 : Nat := 118140960795 + 4103143 * 2 ^ 59
def prefixEnd_4103143 : Nat := 4983230072969 + 3 ^ 40 * 4103143 * 2
def baseEnd_4103143 : Nat := 2106884553131145167842495

theorem tailTrace_4103143 : CollatzResearch.WordTrace tailWord_4103143 prefixEnd_4103143 2106884553131145167842495 := by
  unfold tailWord_4103143
  simp only [CollatzResearch.WordTrace]
  refine ⟨149653919774021146879074083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99769279849347431252716055 149653919774021146879074083)
  ·
    refine ⟨224480879661031720318611125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149653919774021146879074083 224480879661031720318611125)
    ·
      refine ⟨21045082468221723779869793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 224480879661031720318611125 21045082468221723779869793)
      ·
        refine ⟨15783811851166292834902345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21045082468221723779869793 15783811851166292834902345)
        ·
          refine ⟨11837858888374719626176759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15783811851166292834902345 11837858888374719626176759)
          ·
            refine ⟨17756788332562079439265139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11837858888374719626176759 17756788332562079439265139)
            ·
              refine ⟨26635182498843119158897709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17756788332562079439265139 26635182498843119158897709)
              ·
                refine ⟨9988193437066169684586641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26635182498843119158897709 9988193437066169684586641)
                ·
                  refine ⟨7491145077799627263439981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9988193437066169684586641 7491145077799627263439981)
                  ·
                    refine ⟨2809179404174860223789993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7491145077799627263439981 2809179404174860223789993)
                    ·
                      refine ⟨2106884553131145167842495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2809179404174860223789993 2106884553131145167842495)
                      ·
                        rfl

theorem cell23_4103143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 3, 2, 3, 2].length) (baseStart_4103143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4103143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4103143 prefixEnd_4103143 := by exact prefixLift 4103143
  have htrace : WordTrace (prefixWord ++ tailWord_4103143) baseStart_4103143 baseEnd_4103143 := by
    simpa [prefixWord, tailWord_4103143, baseEnd_4103143] using wordTrace_append hprefix tailTrace_4103143
  have hstable : (prefixWord ++ tailWord_4103143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103143).length < 2 ^ (prefixWord ++ tailWord_4103143).sum := by decide
  have hdescent : baseEnd_4103143 < baseStart_4103143 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103153 : List Nat := [1, 2, 2, 2, 4, 2, 3, 1, 1, 5]
def baseStart_4103153 : Nat := 118140960795 + 4103153 * 2 ^ 59
def prefixEnd_4103153 : Nat := 4983230072969 + 3 ^ 40 * 4103153 * 2
def baseEnd_4103153 : Nat := 702296562645896709572483

theorem tailTrace_4103153 : CollatzResearch.WordTrace tailWord_4103153 prefixEnd_4103153 702296562645896709572483 := by
  unfold tailWord_4103153
  simp only [CollatzResearch.WordTrace]
  refine ⟨149654284503984918586938113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99769523002656612391292075 149654284503984918586938113)
  ·
    refine ⟨112240713377988688940203585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149654284503984918586938113 112240713377988688940203585)
    ·
      refine ⟨84180535033491516705152689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112240713377988688940203585 84180535033491516705152689)
      ·
        refine ⟨63135401275118637528864517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84180535033491516705152689 63135401275118637528864517)
        ·
          refine ⟨11837887739084744536662097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63135401275118637528864517 11837887739084744536662097)
          ·
            refine ⟨8878415804313558402496573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11837887739084744536662097 8878415804313558402496573)
            ·
              refine ⟨3329405926617584400936215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8878415804313558402496573 3329405926617584400936215)
              ·
                refine ⟨4994108889926376601404323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3329405926617584400936215 4994108889926376601404323)
                ·
                  refine ⟨7491163334889564902106485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4994108889926376601404323 7491163334889564902106485)
                  ·
                    refine ⟨702296562645896709572483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7491163334889564902106485 702296562645896709572483)
                    ·
                      rfl

theorem cell23_4103153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 3, 1, 1, 5].length) (baseStart_4103153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4103153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4103153 prefixEnd_4103153 := by exact prefixLift 4103153
  have htrace : WordTrace (prefixWord ++ tailWord_4103153) baseStart_4103153 baseEnd_4103153 := by
    simpa [prefixWord, tailWord_4103153, baseEnd_4103153] using wordTrace_append hprefix tailTrace_4103153
  have hstable : (prefixWord ++ tailWord_4103153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103153).length < 2 ^ (prefixWord ++ tailWord_4103153).sum := by decide
  have hdescent : baseEnd_4103153 < baseStart_4103153 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103173 : List Nat := [1, 3, 1, 1, 2, 3, 2, 3, 3, 2, 2]
def baseStart_4103173 : Nat := 118140960795 + 4103173 * 2 ^ 59
def prefixEnd_4103173 : Nat := 4983230072969 + 3 ^ 40 * 4103173 * 2
def baseEnd_4103173 : Nat := 2106899957550780050467357

theorem tailTrace_4103173 : CollatzResearch.WordTrace tailWord_4103173 prefixEnd_4103173 2106899957550780050467357 := by
  unfold tailWord_4103173
  simp only [CollatzResearch.WordTrace]
  refine ⟨149655013963912462002666173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99770009309274974668444115 149655013963912462002666173)
  ·
    refine ⟨56120630236467173250999815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149655013963912462002666173 56120630236467173250999815)
    ·
      refine ⟨84180945354700759876499723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56120630236467173250999815 84180945354700759876499723)
      ·
        refine ⟨126271418032051139814749585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84180945354700759876499723 126271418032051139814749585)
        ·
          refine ⟨94703563524038354861062189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126271418032051139814749585 94703563524038354861062189)
          ·
            refine ⟨35513836321514383072898321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94703563524038354861062189 35513836321514383072898321)
            ·
              refine ⟨26635377241135787304673741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35513836321514383072898321 26635377241135787304673741)
              ·
                refine ⟨9988266465425920239252653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26635377241135787304673741 9988266465425920239252653)
                ·
                  refine ⟨3745599924534720089719745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9988266465425920239252653 3745599924534720089719745)
                  ·
                    refine ⟨2809199943401040067289809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3745599924534720089719745 2809199943401040067289809)
                    ·
                      refine ⟨2106899957550780050467357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2809199943401040067289809 2106899957550780050467357)
                      ·
                        rfl

theorem cell23_4103173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 3, 3, 2, 2].length) (baseStart_4103173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4103173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4103173 prefixEnd_4103173 := by exact prefixLift 4103173
  have htrace : WordTrace (prefixWord ++ tailWord_4103173) baseStart_4103173 baseEnd_4103173 := by
    simpa [prefixWord, tailWord_4103173, baseEnd_4103173] using wordTrace_append hprefix tailTrace_4103173
  have hstable : (prefixWord ++ tailWord_4103173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103173).length < 2 ^ (prefixWord ++ tailWord_4103173).sum := by decide
  have hdescent : baseEnd_4103173 < baseStart_4103173 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103176 : List Nat := [2, 1, 3, 2, 1, 3, 1, 2, 3, 2, 3]
def baseStart_4103176 : Nat := 118140960795 + 4103176 * 2 ^ 59
def prefixEnd_4103176 : Nat := 4983230072969 + 3 ^ 40 * 4103176 * 2
def baseEnd_4103176 : Nat := 2106901497992743538729843

theorem tailTrace_4103176 : CollatzResearch.WordTrace tailWord_4103176 prefixEnd_4103176 2106901497992743538729843 := by
  unfold tailWord_4103176
  simp only [CollatzResearch.WordTrace]
  refine ⟨74827561691450796757512691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99770082255267729010016921 74827561691450796757512691)
  ·
    refine ⟨112241342537176195136269037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74827561691450796757512691 112241342537176195136269037)
    ·
      refine ⟨42090503451441073176100889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112241342537176195136269037 42090503451441073176100889)
      ·
        refine ⟨31567877588580804882075667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42090503451441073176100889 31567877588580804882075667)
        ·
          refine ⟨47351816382871207323113501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31567877588580804882075667 47351816382871207323113501)
          ·
            refine ⟨17756931143576702746167563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47351816382871207323113501 17756931143576702746167563)
            ·
              refine ⟨26635396715365054119251345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17756931143576702746167563 26635396715365054119251345)
              ·
                refine ⟨19976547536523790589438509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26635396715365054119251345 19976547536523790589438509)
                ·
                  refine ⟨7491205326196421471039441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19976547536523790589438509 7491205326196421471039441)
                  ·
                    refine ⟨5618403994647316103279581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7491205326196421471039441 5618403994647316103279581)
                    ·
                      refine ⟨2106901497992743538729843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5618403994647316103279581 2106901497992743538729843)
                      ·
                        rfl

theorem cell23_4103176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 3, 2, 3].length) (baseStart_4103176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4103176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4103176 prefixEnd_4103176 := by exact prefixLift 4103176
  have htrace : WordTrace (prefixWord ++ tailWord_4103176) baseStart_4103176 baseEnd_4103176 := by
    simpa [prefixWord, tailWord_4103176, baseEnd_4103176] using wordTrace_append hprefix tailTrace_4103176
  have hstable : (prefixWord ++ tailWord_4103176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103176).length < 2 ^ (prefixWord ++ tailWord_4103176).sum := by decide
  have hdescent : baseEnd_4103176 < baseStart_4103176 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103179 : List Nat := [1, 1, 1, 1, 6, 2, 3, 8]
def baseStart_4103179 : Nat := 118140960795 + 4103179 * 2 ^ 59
def prefixEnd_4103179 : Nat := 4983230072969 + 3 ^ 40 * 4103179 * 2
def baseEnd_4103179 : Nat := 78033445867952112110827

theorem tailTrace_4103179 : CollatzResearch.WordTrace tailWord_4103179 prefixEnd_4103179 78033445867952112110827 := by
  unfold tailWord_4103179
  simp only [CollatzResearch.WordTrace]
  refine ⟨149655232801890725027384591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99770155201260483351589727 149655232801890725027384591)
  ·
    refine ⟨224482849202836087541076887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149655232801890725027384591 224482849202836087541076887)
    ·
      refine ⟨336724273804254131311615331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224482849202836087541076887 336724273804254131311615331)
      ·
        refine ⟨505086410706381196967422997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336724273804254131311615331 505086410706381196967422997)
        ·
          refine ⟨23675925501861618607847953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 505086410706381196967422997 23675925501861618607847953)
          ·
            refine ⟨17756944126396213955885965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23675925501861618607847953 17756944126396213955885965)
            ·
              refine ⟨6658854047398580233457237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17756944126396213955885965 6658854047398580233457237)
              ·
                refine ⟨78033445867952112110827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6658854047398580233457237 78033445867952112110827)
                ·
                  rfl

theorem cell23_4103179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 8].length) (baseStart_4103179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4103179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4103179 prefixEnd_4103179 := by exact prefixLift 4103179
  have htrace : WordTrace (prefixWord ++ tailWord_4103179) baseStart_4103179 baseEnd_4103179 := by
    simpa [prefixWord, tailWord_4103179, baseEnd_4103179] using wordTrace_append hprefix tailTrace_4103179
  have hstable : (prefixWord ++ tailWord_4103179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103179).length < 2 ^ (prefixWord ++ tailWord_4103179).sum := by decide
  have hdescent : baseEnd_4103179 < baseStart_4103179 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103207 : List Nat := [1, 1, 7, 1, 1, 3, 2, 1, 1, 1, 4]
def baseStart_4103207 : Nat := 118140960795 + 4103207 * 2 ^ 59
def prefixEnd_4103207 : Nat := 4983230072969 + 3 ^ 40 * 4103207 * 2
def baseEnd_4103207 : Nat := 2106917415893032917442201

theorem tailTrace_4103207 : CollatzResearch.WordTrace tailWord_4103207 prefixEnd_4103207 2106917415893032917442201 := by
  unfold tailWord_4103207
  simp only [CollatzResearch.WordTrace]
  refine ⟨149656254045789285809403875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99770836030526190539602583 149656254045789285809403875)
  ·
    refine ⟨224484381068683928714105813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149656254045789285809403875 224484381068683928714105813)
    ·
      refine ⟨5261352681297279579236855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 224484381068683928714105813 5261352681297279579236855)
      ·
        refine ⟨7892029021945919368855283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5261352681297279579236855 7892029021945919368855283)
        ·
          refine ⟨11838043532918879053282925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7892029021945919368855283 11838043532918879053282925)
          ·
            refine ⟨4439266324844579644981097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11838043532918879053282925 4439266324844579644981097)
            ·
              refine ⟨3329449743633434733735823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4439266324844579644981097 3329449743633434733735823)
              ·
                refine ⟨4994174615450152100603735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3329449743633434733735823 4994174615450152100603735)
                ·
                  refine ⟨7491261923175228150905603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4994174615450152100603735 7491261923175228150905603)
                  ·
                    refine ⟨11236892884762842226358405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7491261923175228150905603 11236892884762842226358405)
                    ·
                      refine ⟨2106917415893032917442201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11236892884762842226358405 2106917415893032917442201)
                      ·
                        rfl

theorem cell23_4103207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_4103207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4103207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4103207 prefixEnd_4103207 := by exact prefixLift 4103207
  have htrace : WordTrace (prefixWord ++ tailWord_4103207) baseStart_4103207 baseEnd_4103207 := by
    simpa [prefixWord, tailWord_4103207, baseEnd_4103207] using wordTrace_append hprefix tailTrace_4103207
  have hstable : (prefixWord ++ tailWord_4103207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103207).length < 2 ^ (prefixWord ++ tailWord_4103207).sum := by decide
  have hdescent : baseEnd_4103207 < baseStart_4103207 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103210 : List Nat := [3, 1, 4, 1, 3, 1, 1, 3, 1, 2, 3]
def baseStart_4103210 : Nat := 118140960795 + 4103210 * 2 ^ 59
def prefixEnd_4103210 : Nat := 4983230072969 + 3 ^ 40 * 4103210 * 2
def baseEnd_4103210 : Nat := 2106918956334996405704687

theorem tailTrace_4103210 : CollatzResearch.WordTrace tailWord_4103210 prefixEnd_4103210 2106918956334996405704687 := by
  unfold tailWord_4103210
  simp only [CollatzResearch.WordTrace]
  refine ⟨37414090866194604330440771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99770908976518944881175389 37414090866194604330440771)
  ·
    refine ⟨56121136299291906495661157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37414090866194604330440771 56121136299291906495661157)
    ·
      refine ⟨10522713056117232467936467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56121136299291906495661157 10522713056117232467936467)
      ·
        refine ⟨15784069584175848701904701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10522713056117232467936467 15784069584175848701904701)
        ·
          refine ⟨5919026094065943263214263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15784069584175848701904701 5919026094065943263214263)
          ·
            refine ⟨8878539141098914894821395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5919026094065943263214263 8878539141098914894821395)
            ·
              refine ⟨13317808711648372342232093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8878539141098914894821395 13317808711648372342232093)
              ·
                refine ⟨4994178266868139628337035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13317808711648372342232093 4994178266868139628337035)
                ·
                  refine ⟨7491267400302209442505553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4994178266868139628337035 7491267400302209442505553)
                  ·
                    refine ⟨5618450550226657081879165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7491267400302209442505553 5618450550226657081879165)
                    ·
                      refine ⟨2106918956334996405704687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5618450550226657081879165 2106918956334996405704687)
                      ·
                        rfl

theorem cell23_4103210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_4103210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4103210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4103210 prefixEnd_4103210 := by exact prefixLift 4103210
  have htrace : WordTrace (prefixWord ++ tailWord_4103210) baseStart_4103210 baseEnd_4103210 := by
    simpa [prefixWord, tailWord_4103210, baseEnd_4103210] using wordTrace_append hprefix tailTrace_4103210
  have hstable : (prefixWord ++ tailWord_4103210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103210).length < 2 ^ (prefixWord ++ tailWord_4103210).sum := by decide
  have hdescent : baseEnd_4103210 < baseStart_4103210 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103240 : List Nat := [2, 1, 3, 1, 1, 1, 7, 1, 2, 1, 3]
def baseStart_4103240 : Nat := 118140960795 + 4103240 * 2 ^ 59
def prefixEnd_4103240 : Nat := 4983230072969 + 3 ^ 40 * 4103240 * 2
def baseEnd_4103240 : Nat := 2106934360754631288329549

theorem tailTrace_4103240 : CollatzResearch.WordTrace tailWord_4103240 prefixEnd_4103240 2106934360754631288329549 := by
  unfold tailWord_4103240
  simp only [CollatzResearch.WordTrace]
  refine ⟨74828728827334866222677587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99771638436446488296903449 74828728827334866222677587)
  ·
    refine ⟨112243093241002299334016381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74828728827334866222677587 112243093241002299334016381)
    ·
      refine ⟨42091159965375862250256143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112243093241002299334016381 42091159965375862250256143)
      ·
        refine ⟨63136739948063793375384215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42091159965375862250256143 63136739948063793375384215)
        ·
          refine ⟨94705109922095690063076323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63136739948063793375384215 94705109922095690063076323)
          ·
            refine ⟨142057664883143535094614485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94705109922095690063076323 142057664883143535094614485)
            ·
              refine ⟨3329476520698676603780027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 142057664883143535094614485 3329476520698676603780027)
              ·
                refine ⟨4994214781048014905670041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3329476520698676603780027 4994214781048014905670041)
                ·
                  refine ⟨3745661085786011179252531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4994214781048014905670041 3745661085786011179252531)
                  ·
                    refine ⟨5618491628679016768878797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3745661085786011179252531 5618491628679016768878797)
                    ·
                      refine ⟨2106934360754631288329549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5618491628679016768878797 2106934360754631288329549)
                      ·
                        rfl

theorem cell23_4103240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 7, 1, 2, 1, 3].length) (baseStart_4103240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4103240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4103240 prefixEnd_4103240 := by exact prefixLift 4103240
  have htrace : WordTrace (prefixWord ++ tailWord_4103240) baseStart_4103240 baseEnd_4103240 := by
    simpa [prefixWord, tailWord_4103240, baseEnd_4103240] using wordTrace_append hprefix tailTrace_4103240
  have hstable : (prefixWord ++ tailWord_4103240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103240).length < 2 ^ (prefixWord ++ tailWord_4103240).sum := by decide
  have hdescent : baseEnd_4103240 < baseStart_4103240 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103250 : List Nat := [3, 2, 2, 1, 3, 1, 1, 4, 1, 3, 2]
def baseStart_4103250 : Nat := 118140960795 + 4103250 * 2 ^ 59
def prefixEnd_4103250 : Nat := 4983230072969 + 3 ^ 40 * 4103250 * 2
def baseEnd_4103250 : Nat := 2106939495561176249204503

theorem tailTrace_4103250 : CollatzResearch.WordTrace tailWord_4103250 prefixEnd_4103250 2106939495561176249204503 := by
  unfold tailWord_4103250
  simp only [CollatzResearch.WordTrace]
  refine ⟨37414455596158376038304801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99771881589755669435479469 37414455596158376038304801)
  ·
    refine ⟨28060841697118782028728601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37414455596158376038304801 28060841697118782028728601)
    ·
      refine ⟨21045631272839086521546451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28060841697118782028728601 21045631272839086521546451)
      ·
        refine ⟨31568446909258629782319677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21045631272839086521546451 31568446909258629782319677)
        ·
          refine ⟨11838167590971986168369879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31568446909258629782319677 11838167590971986168369879)
          ·
            refine ⟨17757251386457979252554819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11838167590971986168369879 17757251386457979252554819)
            ·
              refine ⟨26635877079686968878832229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17757251386457979252554819 26635877079686968878832229)
              ·
                refine ⟨4994226952441306664781043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26635877079686968878832229 4994226952441306664781043)
                ·
                  refine ⟨7491340428661959997171565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4994226952441306664781043 7491340428661959997171565)
                  ·
                    refine ⟨2809252660748234998939337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7491340428661959997171565 2809252660748234998939337)
                    ·
                      refine ⟨2106939495561176249204503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2809252660748234998939337 2106939495561176249204503)
                      ·
                        rfl

theorem cell23_4103250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 4, 1, 3, 2].length) (baseStart_4103250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4103250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4103250 prefixEnd_4103250 := by exact prefixLift 4103250
  have htrace : WordTrace (prefixWord ++ tailWord_4103250) baseStart_4103250 baseEnd_4103250 := by
    simpa [prefixWord, tailWord_4103250, baseEnd_4103250] using wordTrace_append hprefix tailTrace_4103250
  have hstable : (prefixWord ++ tailWord_4103250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103250).length < 2 ^ (prefixWord ++ tailWord_4103250).sum := by decide
  have hdescent : baseEnd_4103250 < baseStart_4103250 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103263 : List Nat := [1, 1, 2, 3, 1, 1, 3, 1, 6, 2, 2]
def baseStart_4103263 : Nat := 118140960795 + 4103263 * 2 ^ 59
def prefixEnd_4103263 : Nat := 4983230072969 + 3 ^ 40 * 4103263 * 2
def baseEnd_4103263 : Nat := 2106946170809684698341943

theorem tailTrace_4103263 : CollatzResearch.WordTrace tailWord_4103263 prefixEnd_4103263 2106946170809684698341943 := by
  unfold tailWord_4103263
  simp only [CollatzResearch.WordTrace]
  refine ⟨149658296533586407373442443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99772197689057604915628295 149658296533586407373442443)
  ·
    refine ⟨224487444800379611060163665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149658296533586407373442443 224487444800379611060163665)
    ·
      refine ⟨168365583600284708295122749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224487444800379611060163665 168365583600284708295122749)
      ·
        refine ⟨63137093850106765610671031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168365583600284708295122749 63137093850106765610671031)
        ·
          refine ⟨94705640775160148416006547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63137093850106765610671031 94705640775160148416006547)
          ·
            refine ⟨142058461162740222624009821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94705640775160148416006547 142058461162740222624009821)
            ·
              refine ⟨53271922936027583484003683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142058461162740222624009821 53271922936027583484003683)
              ·
                refine ⟨79907884404041375226005525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53271922936027583484003683 79907884404041375226005525)
                ·
                  refine ⟨3745682081439439463719009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 79907884404041375226005525 3745682081439439463719009)
                  ·
                    refine ⟨2809261561079579597789257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3745682081439439463719009 2809261561079579597789257)
                    ·
                      refine ⟨2106946170809684698341943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2809261561079579597789257 2106946170809684698341943)
                      ·
                        rfl

theorem cell23_4103263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 6, 2, 2].length) (baseStart_4103263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4103263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4103263 prefixEnd_4103263 := by exact prefixLift 4103263
  have htrace : WordTrace (prefixWord ++ tailWord_4103263) baseStart_4103263 baseEnd_4103263 := by
    simpa [prefixWord, tailWord_4103263, baseEnd_4103263] using wordTrace_append hprefix tailTrace_4103263
  have hstable : (prefixWord ++ tailWord_4103263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103263).length < 2 ^ (prefixWord ++ tailWord_4103263).sum := by decide
  have hdescent : baseEnd_4103263 < baseStart_4103263 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
