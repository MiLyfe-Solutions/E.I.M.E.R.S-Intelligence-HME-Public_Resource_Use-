import V185TrunkScan23Chunk0785

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4649072 : List Nat := [2, 1, 1, 1, 5, 2, 1, 1, 1, 6, 2]
def baseStart_4649072 : Nat := 118140960795 + 4649072 * 2 ^ 59
def prefixEnd_4649072 : Nat := 4983230072969 + 3 ^ 40 * 4649072 * 2
def baseEnd_4649072 : Nat := 2387208533359539718119313

theorem tailTrace_4649072 : CollatzResearch.WordTrace tailWord_4649072 prefixEnd_4649072 2387208533359539718119313 := by
  unfold tailWord_4649072
  simp only [CollatzResearch.WordTrace]
  refine ⟨84782793106606808564638735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113043724142142411419518313 84782793106606808564638735)
  ·
    refine ⟨127174189659910212846958103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84782793106606808564638735 127174189659910212846958103)
    ·
      refine ⟨190761284489865319270437155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127174189659910212846958103 190761284489865319270437155)
      ·
        refine ⟨286141926734797978905655733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190761284489865319270437155 286141926734797978905655733)
        ·
          refine ⟨26825805631387310522405225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 286141926734797978905655733 26825805631387310522405225)
          ·
            refine ⟨20119354223540482891803919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26825805631387310522405225 20119354223540482891803919)
            ·
              refine ⟨30179031335310724337705879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20119354223540482891803919 30179031335310724337705879)
              ·
                refine ⟨45268547002966086506558819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30179031335310724337705879 45268547002966086506558819)
                ·
                  refine ⟨67902820504449129759838229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45268547002966086506558819 67902820504449129759838229)
                  ·
                    refine ⟨3182944711146052957492417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 67902820504449129759838229 3182944711146052957492417)
                    ·
                      refine ⟨2387208533359539718119313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3182944711146052957492417 2387208533359539718119313)
                      ·
                        rfl

theorem cell23_4649072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 1, 6, 2].length) (baseStart_4649072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4649072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4649072 prefixEnd_4649072 := by exact prefixLift 4649072
  have htrace : WordTrace (prefixWord ++ tailWord_4649072) baseStart_4649072 baseEnd_4649072 := by
    simpa [prefixWord, tailWord_4649072, baseEnd_4649072] using wordTrace_append hprefix tailTrace_4649072
  have hstable : (prefixWord ++ tailWord_4649072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4649072).length < 2 ^ (prefixWord ++ tailWord_4649072).sum := by decide
  have hdescent : baseEnd_4649072 < baseStart_4649072 := by decide
  rcases family_descends (prefixWord ++ tailWord_4649072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4649092 : List Nat := [2, 3, 2, 1, 2, 1, 3, 1, 1, 4, 3]
def baseStart_4649092 : Nat := 118140960795 + 4649092 * 2 ^ 59
def prefixEnd_4649092 : Nat := 4983230072969 + 3 ^ 40 * 4649092 * 2
def baseEnd_4649092 : Nat := 2387218802972629639869221

theorem tailTrace_4649092 : CollatzResearch.WordTrace tailWord_4649092 prefixEnd_4649092 2387218802972629639869221 := by
  unfold tailWord_4649092
  simp only [CollatzResearch.WordTrace]
  refine ⟨84783157836570580272502765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113044210448760773696670353 84783157836570580272502765)
  ·
    refine ⟨31793684188713967602188537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84783157836570580272502765 31793684188713967602188537)
    ·
      refine ⟨23845263141535475701641403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31793684188713967602188537 23845263141535475701641403)
      ·
        refine ⟨35767894712303213552462105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23845263141535475701641403 35767894712303213552462105)
        ·
          refine ⟨26825921034227410164346579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35767894712303213552462105 26825921034227410164346579)
          ·
            refine ⟨40238881551341115246519869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26825921034227410164346579 40238881551341115246519869)
            ·
              refine ⟨15089580581752918217444951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40238881551341115246519869 15089580581752918217444951)
              ·
                refine ⟨22634370872629377326167427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15089580581752918217444951 22634370872629377326167427)
                ·
                  refine ⟨33951556308944065989251141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22634370872629377326167427 33951556308944065989251141)
                  ·
                    refine ⟨6365916807927012372984589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33951556308944065989251141 6365916807927012372984589)
                    ·
                      refine ⟨2387218802972629639869221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6365916807927012372984589 2387218802972629639869221)
                      ·
                        rfl

theorem cell23_4649092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 1, 4, 3].length) (baseStart_4649092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4649092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4649092 prefixEnd_4649092 := by exact prefixLift 4649092
  have htrace : WordTrace (prefixWord ++ tailWord_4649092) baseStart_4649092 baseEnd_4649092 := by
    simpa [prefixWord, tailWord_4649092, baseEnd_4649092] using wordTrace_append hprefix tailTrace_4649092
  have hstable : (prefixWord ++ tailWord_4649092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4649092).length < 2 ^ (prefixWord ++ tailWord_4649092).sum := by decide
  have hdescent : baseEnd_4649092 < baseStart_4649092 := by decide
  rcases family_descends (prefixWord ++ tailWord_4649092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4649105 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 3]
def baseStart_4649105 : Nat := 118140960795 + 4649105 * 2 ^ 59
def prefixEnd_4649105 : Nat := 4983230072969 + 3 ^ 40 * 4649105 * 2
def baseEnd_4649105 : Nat := 2387225478221138089006661

theorem tailTrace_4649105 : CollatzResearch.WordTrace tailWord_4649105 prefixEnd_4649105 2387225478221138089006661 := by
  unfold tailWord_4649105
  simp only [CollatzResearch.WordTrace]
  refine ⟨169566789822094063765228769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113044526548062709176819179 169566789822094063765228769)
  ·
    refine ⟨127175092366570547823921577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169566789822094063765228769 127175092366570547823921577)
    ·
      refine ⟨95381319274927910867941183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127175092366570547823921577 95381319274927910867941183)
      ·
        refine ⟨143071978912391866301911775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95381319274927910867941183 143071978912391866301911775)
        ·
          refine ⟨214607968368587799452867663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143071978912391866301911775 214607968368587799452867663)
          ·
            refine ⟨321911952552881699179301495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214607968368587799452867663 321911952552881699179301495)
            ·
              refine ⟨482867928829322548768952243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 321911952552881699179301495 482867928829322548768952243)
              ·
                refine ⟨724301893243983823153428365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 482867928829322548768952243 724301893243983823153428365)
                ·
                  refine ⟨271613209966493933682535637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 724301893243983823153428365 271613209966493933682535637)
                  ·
                    refine ⟨6365934608589701570684429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 271613209966493933682535637 6365934608589701570684429)
                    ·
                      refine ⟨2387225478221138089006661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6365934608589701570684429 2387225478221138089006661)
                      ·
                        rfl

theorem cell23_4649105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 3].length) (baseStart_4649105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4649105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4649105 prefixEnd_4649105 := by exact prefixLift 4649105
  have htrace : WordTrace (prefixWord ++ tailWord_4649105) baseStart_4649105 baseEnd_4649105 := by
    simpa [prefixWord, tailWord_4649105, baseEnd_4649105] using wordTrace_append hprefix tailTrace_4649105
  have hstable : (prefixWord ++ tailWord_4649105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4649105).length < 2 ^ (prefixWord ++ tailWord_4649105).sum := by decide
  have hdescent : baseEnd_4649105 < baseStart_4649105 := by decide
  rcases family_descends (prefixWord ++ tailWord_4649105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4649112 : List Nat := [2, 1, 2, 4, 3, 1, 1, 1, 8]
def baseStart_4649112 : Nat := 118140960795 + 4649112 * 2 ^ 59
def prefixEnd_4649112 : Nat := 4983230072969 + 3 ^ 40 * 4649112 * 2
def baseEnd_4649112 : Nat := 265247674731746617957681

theorem tailTrace_4649112 : CollatzResearch.WordTrace tailWord_4649112 prefixEnd_4649112 265247674731746617957681 := by
  unfold tailWord_4649112
  simp only [CollatzResearch.WordTrace]
  refine ⟨84783522566534351980366795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113044696755379135973822393 84783522566534351980366795)
  ·
    refine ⟨127175283849801527970550193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84783522566534351980366795 127175283849801527970550193)
    ·
      refine ⟨95381462887351145977912645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127175283849801527970550193 95381462887351145977912645)
      ·
        refine ⟨17884024291378339870858621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95381462887351145977912645 17884024291378339870858621)
        ·
          refine ⟨6706509109266877451571983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17884024291378339870858621 6706509109266877451571983)
          ·
            refine ⟨10059763663900316177357975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6706509109266877451571983 10059763663900316177357975)
            ·
              refine ⟨15089645495850474266036963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10059763663900316177357975 15089645495850474266036963)
              ·
                refine ⟨22634468243775711399055445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15089645495850474266036963 22634468243775711399055445)
                ·
                  refine ⟨265247674731746617957681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22634468243775711399055445 265247674731746617957681)
                  ·
                    rfl

theorem cell23_4649112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 8].length) (baseStart_4649112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4649112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4649112 prefixEnd_4649112 := by exact prefixLift 4649112
  have htrace : WordTrace (prefixWord ++ tailWord_4649112) baseStart_4649112 baseEnd_4649112 := by
    simpa [prefixWord, tailWord_4649112, baseEnd_4649112] using wordTrace_append hprefix tailTrace_4649112
  have hstable : (prefixWord ++ tailWord_4649112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4649112).length < 2 ^ (prefixWord ++ tailWord_4649112).sum := by decide
  have hdescent : baseEnd_4649112 < baseStart_4649112 := by decide
  rcases family_descends (prefixWord ++ tailWord_4649112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4649149 : List Nat := [1, 4, 1, 2, 1, 1, 1, 5, 2, 3, 2]
def baseStart_4649149 : Nat := 118140960795 + 4649149 * 2 ^ 59
def prefixEnd_4649149 : Nat := 4983230072969 + 3 ^ 40 * 4649149 * 2
def baseEnd_4649149 : Nat := 2387248071369935916856459

theorem tailTrace_4649149 : CollatzResearch.WordTrace tailWord_4649149 prefixEnd_4649149 2387248071369935916856459 := by
  unfold tailWord_4649149
  simp only [CollatzResearch.WordTrace]
  refine ⟨169568394633934659279830501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113045596422623106186553667 169568394633934659279830501)
  ·
    refine ⟨31794073993862748614968219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 169568394633934659279830501 31794073993862748614968219)
    ·
      refine ⟨47691110990794122922452329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31794073993862748614968219 47691110990794122922452329)
      ·
        refine ⟨35768333243095592191839247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47691110990794122922452329 35768333243095592191839247)
        ·
          refine ⟨53652499864643388287758871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35768333243095592191839247 53652499864643388287758871)
          ·
            refine ⟨80478749796965082431638307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53652499864643388287758871 80478749796965082431638307)
            ·
              refine ⟨120718124695447623647457461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80478749796965082431638307 120718124695447623647457461)
              ·
                refine ⟨11317324190198214716949137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 120718124695447623647457461 11317324190198214716949137)
                ·
                  refine ⟨8487993142648661037711853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11317324190198214716949137 8487993142648661037711853)
                  ·
                    refine ⟨3182997428493247889141945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8487993142648661037711853 3182997428493247889141945)
                    ·
                      refine ⟨2387248071369935916856459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3182997428493247889141945 2387248071369935916856459)
                      ·
                        rfl

theorem cell23_4649149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 5, 2, 3, 2].length) (baseStart_4649149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4649149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4649149 prefixEnd_4649149 := by exact prefixLift 4649149
  have htrace : WordTrace (prefixWord ++ tailWord_4649149) baseStart_4649149 baseEnd_4649149 := by
    simpa [prefixWord, tailWord_4649149, baseEnd_4649149] using wordTrace_append hprefix tailTrace_4649149
  have hstable : (prefixWord ++ tailWord_4649149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4649149).length < 2 ^ (prefixWord ++ tailWord_4649149).sum := by decide
  have hdescent : baseEnd_4649149 < baseStart_4649149 := by decide
  rcases family_descends (prefixWord ++ tailWord_4649149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4649150 : List Nat := [4, 2, 1, 1, 5, 1, 1, 3, 1, 4]
def baseStart_4649150 : Nat := 118140960795 + 4649150 * 2 ^ 59
def prefixEnd_4649150 : Nat := 4983230072969 + 3 ^ 40 * 4649150 * 2
def baseEnd_4649150 : Nat := 795749528283530137647985

theorem tailTrace_4649150 : CollatzResearch.WordTrace tailWord_4649150 prefixEnd_4649150 795749528283530137647985 := by
  unfold tailWord_4649150
  simp only [CollatzResearch.WordTrace]
  refine ⟨21196053888366379556327113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113045620737954024300411269 21196053888366379556327113)
  ·
    refine ⟨15897040416274784667245335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21196053888366379556327113 15897040416274784667245335)
    ·
      refine ⟨23845560624412177000868003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15897040416274784667245335 23845560624412177000868003)
      ·
        refine ⟨35768340936618265501302005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23845560624412177000868003 35768340936618265501302005)
        ·
          refine ⟨3353281962807962390747063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35768340936618265501302005 3353281962807962390747063)
          ·
            refine ⟨5029922944211943586120595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3353281962807962390747063 5029922944211943586120595)
            ·
              refine ⟨7544884416317915379180893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5029922944211943586120595 7544884416317915379180893)
              ·
                refine ⟨2829331656119218267192835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7544884416317915379180893 2829331656119218267192835)
                ·
                  refine ⟨4243997484178827400789253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2829331656119218267192835 4243997484178827400789253)
                  ·
                    refine ⟨795749528283530137647985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4243997484178827400789253 795749528283530137647985)
                    ·
                      rfl

theorem cell23_4649150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 3, 1, 4].length) (baseStart_4649150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4649150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4649150 prefixEnd_4649150 := by exact prefixLift 4649150
  have htrace : WordTrace (prefixWord ++ tailWord_4649150) baseStart_4649150 baseEnd_4649150 := by
    simpa [prefixWord, tailWord_4649150, baseEnd_4649150] using wordTrace_append hprefix tailTrace_4649150
  have hstable : (prefixWord ++ tailWord_4649150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4649150).length < 2 ^ (prefixWord ++ tailWord_4649150).sum := by decide
  have hdescent : baseEnd_4649150 < baseStart_4649150 := by decide
  rcases family_descends (prefixWord ++ tailWord_4649150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4649166 : List Nat := [4, 1, 1, 1, 4, 2, 1, 2, 2, 3, 2]
def baseStart_4649166 : Nat := 118140960795 + 4649166 * 2 ^ 59
def prefixEnd_4649166 : Nat := 4983230072969 + 3 ^ 40 * 4649166 * 2
def baseEnd_4649166 : Nat := 2387256800541062350343881

theorem tailTrace_4649166 : CollatzResearch.WordTrace tailWord_4649166 prefixEnd_4649166 2387256800541062350343881 := by
  unfold tailWord_4649166
  simp only [CollatzResearch.WordTrace]
  refine ⟨21196126834359133897899919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113046009783248714122132901 21196126834359133897899919)
  ·
    refine ⟨31794190251538700846849879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21196126834359133897899919 31794190251538700846849879)
    ·
      refine ⟨47691285377308051270274819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31794190251538700846849879 47691285377308051270274819)
      ·
        refine ⟨71536928065962076905412229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47691285377308051270274819 71536928065962076905412229)
        ·
          refine ⟨13413174012367889419764793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71536928065962076905412229 13413174012367889419764793)
          ·
            refine ⟨10059880509275917064823595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13413174012367889419764793 10059880509275917064823595)
            ·
              refine ⟨15089820763913875597235393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10059880509275917064823595 15089820763913875597235393)
              ·
                refine ⟨11317365572935406697926545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15089820763913875597235393 11317365572935406697926545)
                ·
                  refine ⟨8488024179701555023444909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11317365572935406697926545 8488024179701555023444909)
                  ·
                    refine ⟨3183009067388083133791841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8488024179701555023444909 3183009067388083133791841)
                    ·
                      refine ⟨2387256800541062350343881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3183009067388083133791841 2387256800541062350343881)
                      ·
                        rfl

theorem cell23_4649166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 2, 2, 3, 2].length) (baseStart_4649166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4649166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4649166 prefixEnd_4649166 := by exact prefixLift 4649166
  have htrace : WordTrace (prefixWord ++ tailWord_4649166) baseStart_4649166 baseEnd_4649166 := by
    simpa [prefixWord, tailWord_4649166, baseEnd_4649166] using wordTrace_append hprefix tailTrace_4649166
  have hstable : (prefixWord ++ tailWord_4649166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4649166).length < 2 ^ (prefixWord ++ tailWord_4649166).sum := by decide
  have hdescent : baseEnd_4649166 < baseStart_4649166 := by decide
  rcases family_descends (prefixWord ++ tailWord_4649166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4649173 : List Nat := [1, 3, 2, 4, 2, 2, 1, 1, 3, 1, 3]
def baseStart_4649173 : Nat := 118140960795 + 4649173 * 2 ^ 59
def prefixEnd_4649173 : Nat := 4983230072969 + 3 ^ 40 * 4649173 * 2
def baseEnd_4649173 : Nat := 2387260394905643822956349

theorem tailTrace_4649173 : CollatzResearch.WordTrace tailWord_4649173 prefixEnd_4649173 2387260394905643822956349 := by
  unfold tailWord_4649173
  simp only [CollatzResearch.WordTrace]
  refine ⟨169569269985847711378704173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113046179990565140919136115 169569269985847711378704173)
  ·
    refine ⟨63588476244692891767014065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169569269985847711378704173 63588476244692891767014065)
    ·
      refine ⟨47691357183519668825260549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63588476244692891767014065 47691357183519668825260549)
      ·
        refine ⟨8942129471909937904736353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47691357183519668825260549 8942129471909937904736353)
        ·
          refine ⟨6706597103932453428552265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8942129471909937904736353 6706597103932453428552265)
          ·
            refine ⟨5029947827949340071414199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6706597103932453428552265 5029947827949340071414199)
            ·
              refine ⟨7544921741924010107121299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5029947827949340071414199 7544921741924010107121299)
              ·
                refine ⟨11317382612886015160681949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7544921741924010107121299 11317382612886015160681949)
                ·
                  refine ⟨4244018479832255685255731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11317382612886015160681949 4244018479832255685255731)
                  ·
                    refine ⟨6366027719748383527883597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4244018479832255685255731 6366027719748383527883597)
                    ·
                      refine ⟨2387260394905643822956349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6366027719748383527883597 2387260394905643822956349)
                      ·
                        rfl

theorem cell23_4649173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_4649173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4649173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4649173 prefixEnd_4649173 := by exact prefixLift 4649173
  have htrace : WordTrace (prefixWord ++ tailWord_4649173) baseStart_4649173 baseEnd_4649173 := by
    simpa [prefixWord, tailWord_4649173, baseEnd_4649173] using wordTrace_append hprefix tailTrace_4649173
  have hstable : (prefixWord ++ tailWord_4649173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4649173).length < 2 ^ (prefixWord ++ tailWord_4649173).sum := by decide
  have hdescent : baseEnd_4649173 < baseStart_4649173 := by decide
  rcases family_descends (prefixWord ++ tailWord_4649173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4649180 : List Nat := [2, 2, 5, 2, 2, 1, 2, 1, 6]
def baseStart_4649180 : Nat := 118140960795 + 4649180 * 2 ^ 59
def prefixEnd_4649180 : Nat := 4983230072969 + 3 ^ 40 * 4649180 * 2
def baseEnd_4649180 : Nat := 265251554363358366174313

theorem tailTrace_4649180 : CollatzResearch.WordTrace tailWord_4649180 prefixEnd_4649180 265251554363358366174313 := by
  unfold tailWord_4649180
  simp only [CollatzResearch.WordTrace]
  refine ⟨84784762648411175787104497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113046350197881567716139329 84784762648411175787104497)
  ·
    refine ⟨63588571986308381840328373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84784762648411175787104497 63588571986308381840328373)
    ·
      refine ⟨5961428623716410797530785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63588571986308381840328373 5961428623716410797530785)
      ·
        refine ⟨4471071467787308098148089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5961428623716410797530785 4471071467787308098148089)
        ·
          refine ⟨3353303600840481073611067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4471071467787308098148089 3353303600840481073611067)
          ·
            refine ⟨5029955401260721610416601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3353303600840481073611067 5029955401260721610416601)
            ·
              refine ⟨3772466550945541207812451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5029955401260721610416601 3772466550945541207812451)
              ·
                refine ⟨5658699826418311811718677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3772466550945541207812451 5658699826418311811718677)
                ·
                  refine ⟨265251554363358366174313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5658699826418311811718677 265251554363358366174313)
                  ·
                    rfl

theorem cell23_4649180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 2, 1, 6].length) (baseStart_4649180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4649180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4649180 prefixEnd_4649180 := by exact prefixLift 4649180
  have htrace : WordTrace (prefixWord ++ tailWord_4649180) baseStart_4649180 baseEnd_4649180 := by
    simpa [prefixWord, tailWord_4649180, baseEnd_4649180] using wordTrace_append hprefix tailTrace_4649180
  have hstable : (prefixWord ++ tailWord_4649180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4649180).length < 2 ^ (prefixWord ++ tailWord_4649180).sum := by decide
  have hdescent : baseEnd_4649180 < baseStart_4649180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4649180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4649192 : List Nat := [2, 1, 4, 1, 2, 2, 2, 1, 1, 1, 6]
def baseStart_4649192 : Nat := 118140960795 + 4649192 * 2 ^ 59
def prefixEnd_4649192 : Nat := 4983230072969 + 3 ^ 40 * 4649192 * 2
def baseEnd_4649192 : Nat := 2387270151038079248618761

theorem tailTrace_4649192 : CollatzResearch.WordTrace tailWord_4649192 prefixEnd_4649192 2387270151038079248618761 := by
  unfold tailWord_4649192
  simp only [CollatzResearch.WordTrace]
  refine ⟨84784981486389438811822915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113046641981852585082430553 84784981486389438811822915)
  ·
    refine ⟨127177472229584158217734373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84784981486389438811822915 127177472229584158217734373)
    ·
      refine ⟨23845776043047029665825195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127177472229584158217734373 23845776043047029665825195)
      ·
        refine ⟨35768664064570544498737793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23845776043047029665825195 35768664064570544498737793)
        ·
          refine ⟨26826498048427908374053345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35768664064570544498737793 26826498048427908374053345)
          ·
            refine ⟨20119873536320931280540009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26826498048427908374053345 20119873536320931280540009)
            ·
              refine ⟨15089905152240698460405007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20119873536320931280540009 15089905152240698460405007)
              ·
                refine ⟨22634857728361047690607511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15089905152240698460405007 22634857728361047690607511)
                ·
                  refine ⟨33952286592541571535911267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22634857728361047690607511 33952286592541571535911267)
                  ·
                    refine ⟨50928429888812357303866901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33952286592541571535911267 50928429888812357303866901)
                    ·
                      refine ⟨2387270151038079248618761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50928429888812357303866901 2387270151038079248618761)
                      ·
                        rfl

theorem cell23_4649192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_4649192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4649192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4649192 prefixEnd_4649192 := by exact prefixLift 4649192
  have htrace : WordTrace (prefixWord ++ tailWord_4649192) baseStart_4649192 baseEnd_4649192 := by
    simpa [prefixWord, tailWord_4649192, baseEnd_4649192] using wordTrace_append hprefix tailTrace_4649192
  have hstable : (prefixWord ++ tailWord_4649192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4649192).length < 2 ^ (prefixWord ++ tailWord_4649192).sum := by decide
  have hdescent : baseEnd_4649192 < baseStart_4649192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4649192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4649199 : List Nat := [1, 1, 2, 1, 6, 2, 1, 1, 3, 2, 3]
def baseStart_4649199 : Nat := 118140960795 + 4649199 * 2 ^ 59
def prefixEnd_4649199 : Nat := 4983230072969 + 3 ^ 40 * 4649199 * 2
def baseEnd_4649199 : Nat := 2387273745402660721231229

theorem tailTrace_4649199 : CollatzResearch.WordTrace tailWord_4649199 prefixEnd_4649199 2387273745402660721231229 := by
  unfold tailWord_4649199
  simp only [CollatzResearch.WordTrace]
  refine ⟨169570218283753517819150651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113046812189169011879433767 169570218283753517819150651)
  ·
    refine ⟨254355327425630276728725977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169570218283753517819150651 254355327425630276728725977)
    ·
      refine ⟨190766495569222707546544483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 254355327425630276728725977 190766495569222707546544483)
      ·
        refine ⟨286149743353834061319816725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190766495569222707546544483 286149743353834061319816725)
        ·
          refine ⟨13413269219710971624366409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 286149743353834061319816725 13413269219710971624366409)
          ·
            refine ⟨10059951914783228718274807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13413269219710971624366409 10059951914783228718274807)
            ·
              refine ⟨15089927872174843077412211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10059951914783228718274807 15089927872174843077412211)
              ·
                refine ⟨22634891808262264616118317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15089927872174843077412211 22634891808262264616118317)
                ·
                  refine ⟨8488084428098349231044369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22634891808262264616118317 8488084428098349231044369)
                  ·
                    refine ⟨6366063321073761923283277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8488084428098349231044369 6366063321073761923283277)
                    ·
                      refine ⟨2387273745402660721231229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6366063321073761923283277 2387273745402660721231229)
                      ·
                        rfl

theorem cell23_4649199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 3, 2, 3].length) (baseStart_4649199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4649199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4649199 prefixEnd_4649199 := by exact prefixLift 4649199
  have htrace : WordTrace (prefixWord ++ tailWord_4649199) baseStart_4649199 baseEnd_4649199 := by
    simpa [prefixWord, tailWord_4649199, baseEnd_4649199] using wordTrace_append hprefix tailTrace_4649199
  have hstable : (prefixWord ++ tailWord_4649199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4649199).length < 2 ^ (prefixWord ++ tailWord_4649199).sum := by decide
  have hdescent : baseEnd_4649199 < baseStart_4649199 := by decide
  rcases family_descends (prefixWord ++ tailWord_4649199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4649202 : List Nat := [3, 2, 1, 3, 2, 1, 2, 9]
def baseStart_4649202 : Nat := 118140960795 + 4649202 * 2 ^ 59
def prefixEnd_4649202 : Nat := 4983230072969 + 3 ^ 40 * 4649202 * 2
def baseEnd_4649202 : Nat := 88417603179430526277545

theorem tailTrace_4649202 : CollatzResearch.WordTrace tailWord_4649202 prefixEnd_4649202 88417603179430526277545 := by
  unfold tailWord_4649202
  simp only [CollatzResearch.WordTrace]
  refine ⟨42392581925685662332877465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113046885135161766221006573 42392581925685662332877465)
  ·
    refine ⟨31794436444264246749658099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42392581925685662332877465 31794436444264246749658099)
    ·
      refine ⟨47691654666396370124487149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31794436444264246749658099 47691654666396370124487149)
      ·
        refine ⟨17884370499898638796682681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47691654666396370124487149 17884370499898638796682681)
        ·
          refine ⟨13413277874923979097512011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17884370499898638796682681 13413277874923979097512011)
          ·
            refine ⟨20119916812385968646268017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13413277874923979097512011 20119916812385968646268017)
            ·
              refine ⟨15089937609289476484701013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20119916812385968646268017 15089937609289476484701013)
              ·
                refine ⟨88417603179430526277545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15089937609289476484701013 88417603179430526277545)
                ·
                  rfl

theorem cell23_4649202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 9].length) (baseStart_4649202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4649202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4649202 prefixEnd_4649202 := by exact prefixLift 4649202
  have htrace : WordTrace (prefixWord ++ tailWord_4649202) baseStart_4649202 baseEnd_4649202 := by
    simpa [prefixWord, tailWord_4649202, baseEnd_4649202] using wordTrace_append hprefix tailTrace_4649202
  have hstable : (prefixWord ++ tailWord_4649202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4649202).length < 2 ^ (prefixWord ++ tailWord_4649202).sum := by decide
  have hdescent : baseEnd_4649202 < baseStart_4649202 := by decide
  rcases family_descends (prefixWord ++ tailWord_4649202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4649223 : List Nat := [1, 1, 4, 5, 1, 1, 2, 2, 2, 4]
def baseStart_4649223 : Nat := 118140960795 + 4649223 * 2 ^ 59
def prefixEnd_4649223 : Nat := 4983230072969 + 3 ^ 40 * 4649223 * 2
def baseEnd_4649223 : Nat := 795762022979456209110373

theorem tailTrace_4649223 : CollatzResearch.WordTrace tailWord_4649223 prefixEnd_4649223 795762022979456209110373 := by
  unfold tailWord_4649223
  simp only [CollatzResearch.WordTrace]
  refine ⟨169571093635666569918024323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113047395757111046612016215 169571093635666569918024323)
  ·
    refine ⟨254356640453499854877036485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169571093635666569918024323 254356640453499854877036485)
    ·
      refine ⟨47691870085031222789444341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 254356640453499854877036485 47691870085031222789444341)
      ·
        refine ⟨4471112820471677136510407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47691870085031222789444341 4471112820471677136510407)
        ·
          refine ⟨6706669230707515704765611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4471112820471677136510407 6706669230707515704765611)
          ·
            refine ⟨10060003846061273557148417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6706669230707515704765611 10060003846061273557148417)
            ·
              refine ⟨7545002884545955167861313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10060003846061273557148417 7545002884545955167861313)
              ·
                refine ⟨5658752163409466375895985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7545002884545955167861313 5658752163409466375895985)
                ·
                  refine ⟨4244064122557099781921989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5658752163409466375895985 4244064122557099781921989)
                  ·
                    refine ⟨795762022979456209110373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4244064122557099781921989 795762022979456209110373)
                    ·
                      rfl

theorem cell23_4649223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 2, 2, 4].length) (baseStart_4649223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4649223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4649223 prefixEnd_4649223 := by exact prefixLift 4649223
  have htrace : WordTrace (prefixWord ++ tailWord_4649223) baseStart_4649223 baseEnd_4649223 := by
    simpa [prefixWord, tailWord_4649223, baseEnd_4649223] using wordTrace_append hprefix tailTrace_4649223
  have hstable : (prefixWord ++ tailWord_4649223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4649223).length < 2 ^ (prefixWord ++ tailWord_4649223).sum := by decide
  have hdescent : baseEnd_4649223 < baseStart_4649223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4649223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4649272 : List Nat := [2, 1, 2, 1, 3, 1, 2, 3, 2, 1, 5]
def baseStart_4649272 : Nat := 118140960795 + 4649272 * 2 ^ 59
def prefixEnd_4649272 : Nat := 4983230072969 + 3 ^ 40 * 4649272 * 2
def baseEnd_4649272 : Nat := 2387311229490438935618393

theorem tailTrace_4649272 : CollatzResearch.WordTrace tailWord_4649272 prefixEnd_4649272 2387311229490438935618393 := by
  unfold tailWord_4649272
  simp only [CollatzResearch.WordTrace]
  refine ⟨84786440406244525643279035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113048587208326034191038713 84786440406244525643279035)
  ·
    refine ⟨127179660609366788464918553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84786440406244525643279035 127179660609366788464918553)
    ·
      refine ⟨95384745457025091348688915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127179660609366788464918553 95384745457025091348688915)
      ·
        refine ⟨143077118185537637023033373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95384745457025091348688915 143077118185537637023033373)
        ·
          refine ⟨53653919319576613883637515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 143077118185537637023033373 53653919319576613883637515)
          ·
            refine ⟨80480878979364920825456273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53653919319576613883637515 80480878979364920825456273)
            ·
              refine ⟨60360659234523690619092205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80480878979364920825456273 60360659234523690619092205)
              ·
                refine ⟨22635247212946383982159577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60360659234523690619092205 22635247212946383982159577)
                ·
                  refine ⟨16976435409709787986619683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22635247212946383982159577 16976435409709787986619683)
                  ·
                    refine ⟨25464653114564681979929525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16976435409709787986619683 25464653114564681979929525)
                    ·
                      refine ⟨2387311229490438935618393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25464653114564681979929525 2387311229490438935618393)
                      ·
                        rfl

theorem cell23_4649272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 2, 1, 5].length) (baseStart_4649272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4649272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4649272 prefixEnd_4649272 := by exact prefixLift 4649272
  have htrace : WordTrace (prefixWord ++ tailWord_4649272) baseStart_4649272 baseEnd_4649272 := by
    simpa [prefixWord, tailWord_4649272, baseEnd_4649272] using wordTrace_append hprefix tailTrace_4649272
  have hstable : (prefixWord ++ tailWord_4649272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4649272).length < 2 ^ (prefixWord ++ tailWord_4649272).sum := by decide
  have hdescent : baseEnd_4649272 < baseStart_4649272 := by decide
  rcases family_descends (prefixWord ++ tailWord_4649272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4649273 : List Nat := [1, 2, 1, 6, 1, 2, 1, 3, 1, 3, 2]
def baseStart_4649273 : Nat := 118140960795 + 4649273 * 2 ^ 59
def prefixEnd_4649273 : Nat := 4983230072969 + 3 ^ 40 * 4649273 * 2
def baseEnd_4649273 : Nat := 2387311742971093431705889

theorem tailTrace_4649273 : CollatzResearch.WordTrace tailWord_4649273 prefixEnd_4649273 2387311742971093431705889 := by
  unfold tailWord_4649273
  simp only [CollatzResearch.WordTrace]
  refine ⟨169572917285485428457344473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113048611523656952304896315 169572917285485428457344473)
  ·
    refine ⟨127179687964114071343008355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169572917285485428457344473 127179687964114071343008355)
    ·
      refine ⟨190769531946171107014512533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127179687964114071343008355 190769531946171107014512533)
      ·
        refine ⟨8942321809976770641305275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 190769531946171107014512533 8942321809976770641305275)
        ·
          refine ⟨13413482714965155961957913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8942321809976770641305275 13413482714965155961957913)
          ·
            refine ⟨10060112036223866971468435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13413482714965155961957913 10060112036223866971468435)
            ·
              refine ⟨15090168054335800457202653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10060112036223866971468435 15090168054335800457202653)
              ·
                refine ⟨5658813020375925171450995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15090168054335800457202653 5658813020375925171450995)
                ·
                  refine ⟨8488219530563887757176493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5658813020375925171450995 8488219530563887757176493)
                  ·
                    refine ⟨3183082323961457908941185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8488219530563887757176493 3183082323961457908941185)
                    ·
                      refine ⟨2387311742971093431705889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3183082323961457908941185 2387311742971093431705889)
                      ·
                        rfl

theorem cell23_4649273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_4649273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4649273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4649273 prefixEnd_4649273 := by exact prefixLift 4649273
  have htrace : WordTrace (prefixWord ++ tailWord_4649273) baseStart_4649273 baseEnd_4649273 := by
    simpa [prefixWord, tailWord_4649273, baseEnd_4649273] using wordTrace_append hprefix tailTrace_4649273
  have hstable : (prefixWord ++ tailWord_4649273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4649273).length < 2 ^ (prefixWord ++ tailWord_4649273).sum := by decide
  have hdescent : baseEnd_4649273 < baseStart_4649273 := by decide
  rcases family_descends (prefixWord ++ tailWord_4649273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4649329 : List Nat := [1, 2, 2, 2, 1, 2, 1, 2, 1, 7, 2]
def baseStart_4649329 : Nat := 118140960795 + 4649329 * 2 ^ 59
def prefixEnd_4649329 : Nat := 4983230072969 + 3 ^ 40 * 4649329 * 2
def baseEnd_4649329 : Nat := 2387340497887745212605631

theorem tailTrace_4649329 : CollatzResearch.WordTrace tailWord_4649329 prefixEnd_4649329 2387340497887745212605631 := by
  unfold tailWord_4649329
  simp only [CollatzResearch.WordTrace]
  refine ⟨169574959773282550021383041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113049973182188366680922027 169574959773282550021383041)
  ·
    refine ⟨127181219829961912516037281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169574959773282550021383041 127181219829961912516037281)
    ·
      refine ⟨95385914872471434387027961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127181219829961912516037281 95385914872471434387027961)
      ·
        refine ⟨71539436154353575790270971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95385914872471434387027961 71539436154353575790270971)
        ·
          refine ⟨107309154231530363685406457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71539436154353575790270971 107309154231530363685406457)
          ·
            refine ⟨80481865673647772764054843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107309154231530363685406457 80481865673647772764054843)
            ·
              refine ⟨120722798510471659146082265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80481865673647772764054843 120722798510471659146082265)
              ·
                refine ⟨90542098882853744359561699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 120722798510471659146082265 90542098882853744359561699)
                ·
                  refine ⟨135813148324280616539342549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90542098882853744359561699 135813148324280616539342549)
                  ·
                    refine ⟨3183120663850326950140841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 135813148324280616539342549 3183120663850326950140841)
                    ·
                      refine ⟨2387340497887745212605631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3183120663850326950140841 2387340497887745212605631)
                      ·
                        rfl

theorem cell23_4649329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 7, 2].length) (baseStart_4649329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4649329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4649329 prefixEnd_4649329 := by exact prefixLift 4649329
  have htrace : WordTrace (prefixWord ++ tailWord_4649329) baseStart_4649329 baseEnd_4649329 := by
    simpa [prefixWord, tailWord_4649329, baseEnd_4649329] using wordTrace_append hprefix tailTrace_4649329
  have hstable : (prefixWord ++ tailWord_4649329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4649329).length < 2 ^ (prefixWord ++ tailWord_4649329).sum := by decide
  have hdescent : baseEnd_4649329 < baseStart_4649329 := by decide
  rcases family_descends (prefixWord ++ tailWord_4649329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4649339 : List Nat := [1, 1, 1, 1, 1, 8, 1, 2, 2, 5]
def baseStart_4649339 : Nat := 118140960795 + 4649339 * 2 ^ 59
def prefixEnd_4649339 : Nat := 4983230072969 + 3 ^ 40 * 4649339 * 2
def baseEnd_4649339 : Nat := 795781877564763391160195

theorem tailTrace_4649339 : CollatzResearch.WordTrace tailWord_4649339 prefixEnd_4649339 795781877564763391160195 := by
  unfold tailWord_4649339
  simp only [CollatzResearch.WordTrace]
  refine ⟨169575324503246321729247071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113050216335497547819498047 169575324503246321729247071)
  ·
    refine ⟨254362986754869482593870607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169575324503246321729247071 254362986754869482593870607)
    ·
      refine ⟨381544480132304223890805911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254362986754869482593870607 381544480132304223890805911)
      ·
        refine ⟨572316720198456335836208867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 381544480132304223890805911 572316720198456335836208867)
        ·
          refine ⟨858475080297684503754313301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 572316720198456335836208867 858475080297684503754313301)
          ·
            refine ⟨10060254847238490278370859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 858475080297684503754313301 10060254847238490278370859)
            ·
              refine ⟨15090382270857735417556289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10060254847238490278370859 15090382270857735417556289)
              ·
                refine ⟨11317786703143301563167217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15090382270857735417556289 11317786703143301563167217)
                ·
                  refine ⟨8488340027357476172375413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11317786703143301563167217 8488340027357476172375413)
                  ·
                    refine ⟨795781877564763391160195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8488340027357476172375413 795781877564763391160195)
                    ·
                      rfl

theorem cell23_4649339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 2, 2, 5].length) (baseStart_4649339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4649339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4649339 prefixEnd_4649339 := by exact prefixLift 4649339
  have htrace : WordTrace (prefixWord ++ tailWord_4649339) baseStart_4649339 baseEnd_4649339 := by
    simpa [prefixWord, tailWord_4649339, baseEnd_4649339] using wordTrace_append hprefix tailTrace_4649339
  have hstable : (prefixWord ++ tailWord_4649339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4649339).length < 2 ^ (prefixWord ++ tailWord_4649339).sum := by decide
  have hdescent : baseEnd_4649339 < baseStart_4649339 := by decide
  rcases family_descends (prefixWord ++ tailWord_4649339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4649354 : List Nat := [3, 1, 2, 5, 1, 2, 2, 1, 2, 2, 2]
def baseStart_4649354 : Nat := 118140960795 + 4649354 * 2 ^ 59
def prefixEnd_4649354 : Nat := 4983230072969 + 3 ^ 40 * 4649354 * 2
def baseEnd_4649354 : Nat := 2387353334904107614793017

theorem tailTrace_4649354 : CollatzResearch.WordTrace tailWord_4649354 prefixEnd_4649354 2387353334904107614793017 := by
  unfold tailWord_4649354
  simp only [CollatzResearch.WordTrace]
  refine ⟨42393967899547994822760779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113050581065461319527362077 42393967899547994822760779)
  ·
    refine ⟨63590951849321992234141169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42393967899547994822760779 63590951849321992234141169)
    ·
      refine ⟨47693213886991494175605877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63590951849321992234141169 47693213886991494175605877)
      ·
        refine ⟨4471238801905452578963051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47693213886991494175605877 4471238801905452578963051)
        ·
          refine ⟨6706858202858178868444577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4471238801905452578963051 6706858202858178868444577)
          ·
            refine ⟨5030143652143634151333433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6706858202858178868444577 5030143652143634151333433)
            ·
              refine ⟨3772607739107725613500075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5030143652143634151333433 3772607739107725613500075)
              ·
                refine ⟨5658911608661588420250113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3772607739107725613500075 5658911608661588420250113)
                ·
                  refine ⟨4244183706496191315187585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5658911608661588420250113 4244183706496191315187585)
                  ·
                    refine ⟨3183137779872143486390689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4244183706496191315187585 3183137779872143486390689)
                    ·
                      refine ⟨2387353334904107614793017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3183137779872143486390689 2387353334904107614793017)
                      ·
                        rfl

theorem cell23_4649354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_4649354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4649354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4649354 prefixEnd_4649354 := by exact prefixLift 4649354
  have htrace : WordTrace (prefixWord ++ tailWord_4649354) baseStart_4649354 baseEnd_4649354 := by
    simpa [prefixWord, tailWord_4649354, baseEnd_4649354] using wordTrace_append hprefix tailTrace_4649354
  have hstable : (prefixWord ++ tailWord_4649354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4649354).length < 2 ^ (prefixWord ++ tailWord_4649354).sum := by decide
  have hdescent : baseEnd_4649354 < baseStart_4649354 := by decide
  rcases family_descends (prefixWord ++ tailWord_4649354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4649369 : List Nat := [1, 2, 1, 2, 1, 4, 2, 1, 5, 4]
def baseStart_4649369 : Nat := 118140960795 + 4649369 * 2 ^ 59
def prefixEnd_4649369 : Nat := 4983230072969 + 3 ^ 40 * 4649369 * 2
def baseEnd_4649369 : Nat := 795787012371308352035149

theorem tailTrace_4649369 : CollatzResearch.WordTrace tailWord_4649369 prefixEnd_4649369 795787012371308352035149 := by
  unfold tailWord_4649369
  simp only [CollatzResearch.WordTrace]
  refine ⟨169576418693137636852839161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113050945795425091235226107 169576418693137636852839161)
  ·
    refine ⟨127182314019853227639629371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169576418693137636852839161 127182314019853227639629371)
    ·
      refine ⟨190773471029779841459444057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127182314019853227639629371 190773471029779841459444057)
      ·
        refine ⟨143080103272334881094583043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190773471029779841459444057 143080103272334881094583043)
        ·
          refine ⟨214620154908502321641874565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143080103272334881094583043 214620154908502321641874565)
          ·
            refine ⟨40241279045344185307851481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 214620154908502321641874565 40241279045344185307851481)
            ·
              refine ⟨30180959284008138980888611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40241279045344185307851481 30180959284008138980888611)
              ·
                refine ⟨45271438926012208471332917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30180959284008138980888611 45271438926012208471332917)
                ·
                  refine ⟨4244197399313644544187461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45271438926012208471332917 4244197399313644544187461)
                  ·
                    refine ⟨795787012371308352035149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4244197399313644544187461 795787012371308352035149)
                    ·
                      rfl

theorem cell23_4649369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 5, 4].length) (baseStart_4649369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4649369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4649369 prefixEnd_4649369 := by exact prefixLift 4649369
  have htrace : WordTrace (prefixWord ++ tailWord_4649369) baseStart_4649369 baseEnd_4649369 := by
    simpa [prefixWord, tailWord_4649369, baseEnd_4649369] using wordTrace_append hprefix tailTrace_4649369
  have hstable : (prefixWord ++ tailWord_4649369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4649369).length < 2 ^ (prefixWord ++ tailWord_4649369).sum := by decide
  have hdescent : baseEnd_4649369 < baseStart_4649369 := by decide
  rcases family_descends (prefixWord ++ tailWord_4649369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4649376 : List Nat := [2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 4]
def baseStart_4649376 : Nat := 118140960795 + 4649376 * 2 ^ 59
def prefixEnd_4649376 : Nat := 4983230072969 + 3 ^ 40 * 4649376 * 2
def baseEnd_4649376 : Nat := 2387364631478506528717915

theorem tailTrace_4649376 : CollatzResearch.WordTrace tailWord_4649376 prefixEnd_4649376 2387364631478506528717915 := by
  unfold tailWord_4649376
  simp only [CollatzResearch.WordTrace]
  refine ⟨84788337002056138524171991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113051116002741518032229321 84788337002056138524171991)
  ·
    refine ⟨127182505503084207786257987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84788337002056138524171991 127182505503084207786257987)
    ·
      refine ⟨190773758254626311679386981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127182505503084207786257987 190773758254626311679386981)
      ·
        refine ⟨35770079672742433439885059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 190773758254626311679386981 35770079672742433439885059)
        ·
          refine ⟨53655119509113650159827589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35770079672742433439885059 53655119509113650159827589)
          ·
            refine ⟨10060334907958809404967673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53655119509113650159827589 10060334907958809404967673)
            ·
              refine ⟨7545251180969107053725755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10060334907958809404967673 7545251180969107053725755)
              ·
                refine ⟨11317876771453660580588633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7545251180969107053725755 11317876771453660580588633)
                ·
                  refine ⟨8488407578590245435441475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11317876771453660580588633 8488407578590245435441475)
                  ·
                    refine ⟨12732611367885368153162213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8488407578590245435441475 12732611367885368153162213)
                    ·
                      refine ⟨2387364631478506528717915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12732611367885368153162213 2387364631478506528717915)
                      ·
                        rfl

theorem cell23_4649376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 4].length) (baseStart_4649376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4649376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4649376 prefixEnd_4649376 := by exact prefixLift 4649376
  have htrace : WordTrace (prefixWord ++ tailWord_4649376) baseStart_4649376 baseEnd_4649376 := by
    simpa [prefixWord, tailWord_4649376, baseEnd_4649376] using wordTrace_append hprefix tailTrace_4649376
  have hstable : (prefixWord ++ tailWord_4649376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4649376).length < 2 ^ (prefixWord ++ tailWord_4649376).sum := by decide
  have hdescent : baseEnd_4649376 < baseStart_4649376 := by decide
  rcases family_descends (prefixWord ++ tailWord_4649376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4649399 : List Nat := [1, 1, 3, 1, 3, 3, 1, 4, 6]
def baseStart_4649399 : Nat := 118140960795 + 4649399 * 2 ^ 59
def prefixEnd_4649399 : Nat := 4983230072969 + 3 ^ 40 * 4649399 * 2
def baseEnd_4649399 : Nat := 265264049059284437636701

theorem tailTrace_4649399 : CollatzResearch.WordTrace tailWord_4649399 prefixEnd_4649399 265264049059284437636701 := by
  unfold tailWord_4649399
  simp only [CollatzResearch.WordTrace]
  refine ⟨169577512883028951976431251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113051675255352634650954167 169577512883028951976431251)
  ·
    refine ⟨254366269324543427964646877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169577512883028951976431251 254366269324543427964646877)
    ·
      refine ⟨95387350996703785486742579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 254366269324543427964646877 95387350996703785486742579)
      ·
        refine ⟨143081026495055678230113869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95387350996703785486742579 143081026495055678230113869)
        ·
          refine ⟨53655384935645879336292701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 143081026495055678230113869 53655384935645879336292701)
          ·
            refine ⟨20120769350867204751109763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53655384935645879336292701 20120769350867204751109763)
            ·
              refine ⟨30181154026300807126664645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20120769350867204751109763 30181154026300807126664645)
              ·
                refine ⟨5658966379931401336249621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30181154026300807126664645 5658966379931401336249621)
                ·
                  refine ⟨265264049059284437636701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5658966379931401336249621 265264049059284437636701)
                  ·
                    rfl

theorem cell23_4649399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 4, 6].length) (baseStart_4649399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4649399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4649399 prefixEnd_4649399 := by exact prefixLift 4649399
  have htrace : WordTrace (prefixWord ++ tailWord_4649399) baseStart_4649399 baseEnd_4649399 := by
    simpa [prefixWord, tailWord_4649399, baseEnd_4649399] using wordTrace_append hprefix tailTrace_4649399
  have hstable : (prefixWord ++ tailWord_4649399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4649399).length < 2 ^ (prefixWord ++ tailWord_4649399).sum := by decide
  have hdescent : baseEnd_4649399 < baseStart_4649399 := by decide
  rcases family_descends (prefixWord ++ tailWord_4649399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4649449 : List Nat := [1, 2, 1, 1, 1, 2, 1, 4, 5, 1, 4]
def baseStart_4649449 : Nat := 118140960795 + 4649449 * 2 ^ 59
def prefixEnd_4649449 : Nat := 4983230072969 + 3 ^ 40 * 4649449 * 2
def baseEnd_4649449 : Nat := 2387402115566284743105079

theorem tailTrace_4649449 : CollatzResearch.WordTrace tailWord_4649449 prefixEnd_4649449 2387402115566284743105079 := by
  unfold tailWord_4649449
  simp only [CollatzResearch.WordTrace]
  refine ⟨169579336532847810515751401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113052891021898540343834267 169579336532847810515751401)
  ·
    refine ⟨127184502399635857886813551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169579336532847810515751401 127184502399635857886813551)
    ·
      refine ⟨190776753599453786830220327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127184502399635857886813551 190776753599453786830220327)
      ·
        refine ⟨286165130399180680245330491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190776753599453786830220327 286165130399180680245330491)
        ·
          refine ⟨429247695598771020367995737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 286165130399180680245330491 429247695598771020367995737)
          ·
            refine ⟨321935771699078265275996803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 429247695598771020367995737 321935771699078265275996803)
            ·
              refine ⟨482903657548617397913995205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 321935771699078265275996803 482903657548617397913995205)
              ·
                refine ⟨90544435790365762108874101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 482903657548617397913995205 90544435790365762108874101)
                ·
                  refine ⟨8488540855346790197706947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 90544435790365762108874101 8488540855346790197706947)
                  ·
                    refine ⟨12732811283020185296560421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8488540855346790197706947 12732811283020185296560421)
                    ·
                      refine ⟨2387402115566284743105079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12732811283020185296560421 2387402115566284743105079)
                      ·
                        rfl

theorem cell23_4649449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 5, 1, 4].length) (baseStart_4649449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4649449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4649449 prefixEnd_4649449 := by exact prefixLift 4649449
  have htrace : WordTrace (prefixWord ++ tailWord_4649449) baseStart_4649449 baseEnd_4649449 := by
    simpa [prefixWord, tailWord_4649449, baseEnd_4649449] using wordTrace_append hprefix tailTrace_4649449
  have hstable : (prefixWord ++ tailWord_4649449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4649449).length < 2 ^ (prefixWord ++ tailWord_4649449).sum := by decide
  have hdescent : baseEnd_4649449 < baseStart_4649449 := by decide
  rcases family_descends (prefixWord ++ tailWord_4649449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4649483 : List Nat := [1, 1, 1, 1, 7, 2, 2, 2, 1, 1, 4]
def baseStart_4649483 : Nat := 118140960795 + 4649483 * 2 ^ 59
def prefixEnd_4649483 : Nat := 4983230072969 + 3 ^ 40 * 4649483 * 2
def baseEnd_4649483 : Nat := 2387419573908537610079923

theorem tailTrace_4649483 : CollatzResearch.WordTrace tailWord_4649483 prefixEnd_4649483 2387419573908537610079923 := by
  unfold tailWord_4649483
  simp only [CollatzResearch.WordTrace]
  refine ⟨169580576614724634322489103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113053717743149756214992735 169580576614724634322489103)
  ·
    refine ⟨254370864922086951483733655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169580576614724634322489103 254370864922086951483733655)
    ·
      refine ⟨381556297383130427225600483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254370864922086951483733655 381556297383130427225600483)
      ·
        refine ⟨572334446074695640838400725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 381556297383130427225600483 572334446074695640838400725)
        ·
          refine ⟨13414088579875679082150017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 572334446074695640838400725 13414088579875679082150017)
          ·
            refine ⟨10060566434906759311612513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13414088579875679082150017 10060566434906759311612513)
            ·
              refine ⟨7545424826180069483709385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10060566434906759311612513 7545424826180069483709385)
              ·
                refine ⟨5659068619635052112782039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7545424826180069483709385 5659068619635052112782039)
                ·
                  refine ⟨8488602929452578169173059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5659068619635052112782039 8488602929452578169173059)
                  ·
                    refine ⟨12732904394178867253759589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8488602929452578169173059 12732904394178867253759589)
                    ·
                      refine ⟨2387419573908537610079923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12732904394178867253759589 2387419573908537610079923)
                      ·
                        rfl

theorem cell23_4649483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 2, 1, 1, 4].length) (baseStart_4649483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4649483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4649483 prefixEnd_4649483 := by exact prefixLift 4649483
  have htrace : WordTrace (prefixWord ++ tailWord_4649483) baseStart_4649483 baseEnd_4649483 := by
    simpa [prefixWord, tailWord_4649483, baseEnd_4649483] using wordTrace_append hprefix tailTrace_4649483
  have hstable : (prefixWord ++ tailWord_4649483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4649483).length < 2 ^ (prefixWord ++ tailWord_4649483).sum := by decide
  have hdescent : baseEnd_4649483 < baseStart_4649483 := by decide
  rcases family_descends (prefixWord ++ tailWord_4649483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4649511 : List Nat := [1, 1, 7, 2, 1, 1, 3, 2, 1, 1, 3]
def baseStart_4649511 : Nat := 118140960795 + 4649511 * 2 ^ 59
def prefixEnd_4649511 : Nat := 4983230072969 + 3 ^ 40 * 4649511 * 2
def baseEnd_4649511 : Nat := 2387433951366863500529795

theorem tailTrace_4649511 : CollatzResearch.WordTrace tailWord_4649511 prefixEnd_4649511 2387433951366863500529795 := by
  unfold tailWord_4649511
  simp only [CollatzResearch.WordTrace]
  refine ⟨169581597858623195104508387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113054398572415463403005591 169581597858623195104508387)
  ·
    refine ⟨254372396787934792656762581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169581597858623195104508387 254372396787934792656762581)
    ·
      refine ⟨5961853049717221702892873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 254372396787934792656762581 5961853049717221702892873)
      ·
        refine ⟨4471389787287916277169655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5961853049717221702892873 4471389787287916277169655)
        ·
          refine ⟨6707084680931874415754483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4471389787287916277169655 6707084680931874415754483)
          ·
            refine ⟨10060627021397811623631725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6707084680931874415754483 10060627021397811623631725)
            ·
              refine ⟨3772735133024179358861897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10060627021397811623631725 3772735133024179358861897)
              ·
                refine ⟨2829551349768134519146423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3772735133024179358861897 2829551349768134519146423)
                ·
                  refine ⟨4244327024652201778719635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2829551349768134519146423 4244327024652201778719635)
                  ·
                    refine ⟨6366490536978302668079453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4244327024652201778719635 6366490536978302668079453)
                    ·
                      refine ⟨2387433951366863500529795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6366490536978302668079453 2387433951366863500529795)
                      ·
                        rfl

theorem cell23_4649511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_4649511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4649511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4649511 prefixEnd_4649511 := by exact prefixLift 4649511
  have htrace : WordTrace (prefixWord ++ tailWord_4649511) baseStart_4649511 baseEnd_4649511 := by
    simpa [prefixWord, tailWord_4649511, baseEnd_4649511] using wordTrace_append hprefix tailTrace_4649511
  have hstable : (prefixWord ++ tailWord_4649511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4649511).length < 2 ^ (prefixWord ++ tailWord_4649511).sum := by decide
  have hdescent : baseEnd_4649511 < baseStart_4649511 := by decide
  rcases family_descends (prefixWord ++ tailWord_4649511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4649534 : List Nat := [4, 2, 1, 4, 2, 1, 1, 2, 1, 1, 4]
def baseStart_4649534 : Nat := 118140960795 + 4649534 * 2 ^ 59
def prefixEnd_4649534 : Nat := 4983230072969 + 3 ^ 40 * 4649534 * 2
def baseEnd_4649534 : Nat := 2387445761421916910542189

theorem tailTrace_4649534 : CollatzResearch.WordTrace tailWord_4649534 prefixEnd_4649534 2387445761421916910542189 := by
  unfold tailWord_4649534
  simp only [CollatzResearch.WordTrace]
  refine ⟨21197804592192483754074457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113054957825026580021730437 21197804592192483754074457)
  ·
    refine ⟨15898353444144362815555843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21197804592192483754074457 15898353444144362815555843)
    ·
      refine ⟨23847530166216544223333765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15898353444144362815555843 23847530166216544223333765)
      ·
        refine ⟨4471411906165602041875081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23847530166216544223333765 4471411906165602041875081)
        ·
          refine ⟨3353558929624201531406311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4471411906165602041875081 3353558929624201531406311)
          ·
            refine ⟨5030338394436302297109467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3353558929624201531406311 5030338394436302297109467)
            ·
              refine ⟨7545507591654453445664201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5030338394436302297109467 7545507591654453445664201)
              ·
                refine ⟨5659130693740840084248151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7545507591654453445664201 5659130693740840084248151)
                ·
                  refine ⟨8488696040611260126372227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5659130693740840084248151 8488696040611260126372227)
                  ·
                    refine ⟨12733044060916890189558341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8488696040611260126372227 12733044060916890189558341)
                    ·
                      refine ⟨2387445761421916910542189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12733044060916890189558341 2387445761421916910542189)
                      ·
                        rfl

theorem cell23_4649534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_4649534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4649534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4649534 prefixEnd_4649534 := by exact prefixLift 4649534
  have htrace : WordTrace (prefixWord ++ tailWord_4649534) baseStart_4649534 baseEnd_4649534 := by
    simpa [prefixWord, tailWord_4649534, baseEnd_4649534] using wordTrace_append hprefix tailTrace_4649534
  have hstable : (prefixWord ++ tailWord_4649534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4649534).length < 2 ^ (prefixWord ++ tailWord_4649534).sum := by decide
  have hdescent : baseEnd_4649534 < baseStart_4649534 := by decide
  rcases family_descends (prefixWord ++ tailWord_4649534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4649630 : List Nat := [4, 3, 1, 1, 1, 1, 1, 6, 5]
def baseStart_4649630 : Nat := 118140960795 + 4649630 * 2 ^ 59
def prefixEnd_4649630 : Nat := 4983230072969 + 3 ^ 40 * 4649630 * 2
def baseEnd_4649630 : Nat := 265277228396083170549083

theorem tailTrace_4649630 : CollatzResearch.WordTrace tailWord_4649630 prefixEnd_4649630 265277228396083170549083 := by
  unfold tailWord_4649630
  simp only [CollatzResearch.WordTrace]
  refine ⟨21198242268149009803511293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113057292096794718952060229 21198242268149009803511293)
  ·
    refine ⟨7949340850555878676316735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21198242268149009803511293 7949340850555878676316735)
    ·
      refine ⟨11924011275833818014475103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7949340850555878676316735 11924011275833818014475103)
      ·
        refine ⟨17886016913750727021712655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11924011275833818014475103 17886016913750727021712655)
        ·
          refine ⟨26829025370626090532568983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17886016913750727021712655 26829025370626090532568983)
          ·
            refine ⟨40243538055939135798853475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26829025370626090532568983 40243538055939135798853475)
            ·
              refine ⟨60365307083908703698280213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40243538055939135798853475 60365307083908703698280213)
              ·
                refine ⟨2829623769558220485856885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 60365307083908703698280213 2829623769558220485856885)
                ·
                  refine ⟨265277228396083170549083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2829623769558220485856885 265277228396083170549083)
                  ·
                    rfl

theorem cell23_4649630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_4649630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4649630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4649630 prefixEnd_4649630 := by exact prefixLift 4649630
  have htrace : WordTrace (prefixWord ++ tailWord_4649630) baseStart_4649630 baseEnd_4649630 := by
    simpa [prefixWord, tailWord_4649630, baseEnd_4649630] using wordTrace_append hprefix tailTrace_4649630
  have hstable : (prefixWord ++ tailWord_4649630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4649630).length < 2 ^ (prefixWord ++ tailWord_4649630).sum := by decide
  have hdescent : baseEnd_4649630 < baseStart_4649630 := by decide
  rcases family_descends (prefixWord ++ tailWord_4649630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4649636 : List Nat := [2, 3, 1, 2, 2, 1, 2, 1, 1, 1, 7]
def baseStart_4649636 : Nat := 118140960795 + 4649636 * 2 ^ 59
def prefixEnd_4649636 : Nat := 4983230072969 + 3 ^ 40 * 4649636 * 2
def baseEnd_4649636 : Nat := 2387498136448675511466719

theorem tailTrace_4649636 : CollatzResearch.WordTrace tailWord_4649636 prefixEnd_4649636 2387498136448675511466719 := by
  unfold tailWord_4649636
  simp only [CollatzResearch.WordTrace]
  refine ⟨84793078491585170726404381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113057437988780227635205841 84793078491585170726404381)
  ·
    refine ⟨31797404434344439022401643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84793078491585170726404381 31797404434344439022401643)
    ·
      refine ⟨47696106651516658533602465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31797404434344439022401643 47696106651516658533602465)
      ·
        refine ⟨35772079988637493900201849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47696106651516658533602465 35772079988637493900201849)
        ·
          refine ⟨26829059991478120425151387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35772079988637493900201849 26829059991478120425151387)
          ·
            refine ⟨40243589987217180637727081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26829059991478120425151387 40243589987217180637727081)
            ·
              refine ⟨30182692490412885478295311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40243589987217180637727081 30182692490412885478295311)
              ·
                refine ⟨45274038735619328217442967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30182692490412885478295311 45274038735619328217442967)
                ·
                  refine ⟨67911058103428992326164451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45274038735619328217442967 67911058103428992326164451)
                  ·
                    refine ⟨101866587155143488489246677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 67911058103428992326164451 101866587155143488489246677)
                    ·
                      refine ⟨2387498136448675511466719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 101866587155143488489246677 2387498136448675511466719)
                      ·
                        rfl

theorem cell23_4649636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_4649636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4649636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4649636 prefixEnd_4649636 := by exact prefixLift 4649636
  have htrace : WordTrace (prefixWord ++ tailWord_4649636) baseStart_4649636 baseEnd_4649636 := by
    simpa [prefixWord, tailWord_4649636, baseEnd_4649636] using wordTrace_append hprefix tailTrace_4649636
  have hstable : (prefixWord ++ tailWord_4649636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4649636).length < 2 ^ (prefixWord ++ tailWord_4649636).sum := by decide
  have hdescent : baseEnd_4649636 < baseStart_4649636 := by decide
  rcases family_descends (prefixWord ++ tailWord_4649636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4649677 : List Nat := [1, 6, 2, 1, 2, 1, 1, 2, 2, 5]
def baseStart_4649677 : Nat := 118140960795 + 4649677 * 2 ^ 59
def prefixEnd_4649677 : Nat := 4983230072969 + 3 ^ 40 * 4649677 * 2
def baseEnd_4649677 : Nat := 795839729718503283684677

theorem tailTrace_4649677 : CollatzResearch.WordTrace tailWord_4649677 prefixEnd_4649677 795839729718503283684677 := by
  unfold tailWord_4649677
  simp only [CollatzResearch.WordTrace]
  refine ⟨169587652376021805455051285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113058434917347870303367523 169587652376021805455051285)
  ·
    refine ⟨7949421205126022130705529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 169587652376021805455051285 7949421205126022130705529)
    ·
      refine ⟨5962065903844516598029147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7949421205126022130705529 5962065903844516598029147)
      ·
        refine ⟨8943098855766774897043721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5962065903844516598029147 8943098855766774897043721)
        ·
          refine ⟨6707324141825081172782791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8943098855766774897043721 6707324141825081172782791)
          ·
            refine ⟨10060986212737621759174187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6707324141825081172782791 10060986212737621759174187)
            ·
              refine ⟨15091479319106432638761281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10060986212737621759174187 15091479319106432638761281)
              ·
                refine ⟨11318609489329824479070961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15091479319106432638761281 11318609489329824479070961)
                ·
                  refine ⟨8488957116997368359303221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11318609489329824479070961 8488957116997368359303221)
                  ·
                    refine ⟨795839729718503283684677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8488957116997368359303221 795839729718503283684677)
                    ·
                      rfl

theorem cell23_4649677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_4649677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4649677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4649677 prefixEnd_4649677 := by exact prefixLift 4649677
  have htrace : WordTrace (prefixWord ++ tailWord_4649677) baseStart_4649677 baseEnd_4649677 := by
    simpa [prefixWord, tailWord_4649677, baseEnd_4649677] using wordTrace_append hprefix tailTrace_4649677
  have hstable : (prefixWord ++ tailWord_4649677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4649677).length < 2 ^ (prefixWord ++ tailWord_4649677).sum := by decide
  have hdescent : baseEnd_4649677 < baseStart_4649677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4649677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4649723 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 5, 5, 2]
def baseStart_4649723 : Nat := 118140960795 + 4649723 * 2 ^ 59
def prefixEnd_4649723 : Nat := 4983230072969 + 3 ^ 40 * 4649723 * 2
def baseEnd_4649723 : Nat := 2387542809265616671078819

theorem tailTrace_4649723 : CollatzResearch.WordTrace tailWord_4649723 prefixEnd_4649723 2387542809265616671078819 := by
  unfold tailWord_4649723
  simp only [CollatzResearch.WordTrace]
  refine ⟨169589330133855155311225823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113059553422570103540817215 169589330133855155311225823)
  ·
    refine ⟨254383995200782732966838735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169589330133855155311225823 254383995200782732966838735)
    ·
      refine ⟨381575992801174099450258103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254383995200782732966838735 381575992801174099450258103)
      ·
        refine ⟨572363989201761149175387155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 381575992801174099450258103 572363989201761149175387155)
        ·
          refine ⟨858545983802641723763080733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 572363989201761149175387155 858545983802641723763080733)
          ·
            refine ⟨321954743925990646411155275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 858545983802641723763080733 321954743925990646411155275)
            ·
              refine ⟨482932115888985969616732913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 321954743925990646411155275 482932115888985969616732913)
              ·
                refine ⟨362199086916739477212549685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 482932115888985969616732913 362199086916739477212549685)
                ·
                  refine ⟨33956164398444325988676533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 362199086916739477212549685 33956164398444325988676533)
                  ·
                    refine ⟨3183390412354155561438425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33956164398444325988676533 3183390412354155561438425)
                    ·
                      refine ⟨2387542809265616671078819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3183390412354155561438425 2387542809265616671078819)
                      ·
                        rfl

theorem cell23_4649723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 5, 2].length) (baseStart_4649723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4649723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4649723 prefixEnd_4649723 := by exact prefixLift 4649723
  have htrace : WordTrace (prefixWord ++ tailWord_4649723) baseStart_4649723 baseEnd_4649723 := by
    simpa [prefixWord, tailWord_4649723, baseEnd_4649723] using wordTrace_append hprefix tailTrace_4649723
  have hstable : (prefixWord ++ tailWord_4649723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4649723).length < 2 ^ (prefixWord ++ tailWord_4649723).sum := by decide
  have hdescent : baseEnd_4649723 < baseStart_4649723 := by decide
  rcases family_descends (prefixWord ++ tailWord_4649723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4649733 : List Nat := [1, 3, 1, 1, 2, 1, 1, 7, 1, 5]
def baseStart_4649733 : Nat := 118140960795 + 4649733 * 2 ^ 59
def prefixEnd_4649733 : Nat := 4983230072969 + 3 ^ 40 * 4649733 * 2
def baseEnd_4649733 : Nat := 795849314690720543984591

theorem tailTrace_4649733 : CollatzResearch.WordTrace tailWord_4649733 prefixEnd_4649733 795849314690720543984591 := by
  unfold tailWord_4649733
  simp only [CollatzResearch.WordTrace]
  refine ⟨169589694863818927019089853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113059796575879284679393235 169589694863818927019089853)
  ·
    refine ⟨63596135573932097632158695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169589694863818927019089853 63596135573932097632158695)
    ·
      refine ⟨95394203360898146448238043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63596135573932097632158695 95394203360898146448238043)
      ·
        refine ⟨143091305041347219672357065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95394203360898146448238043 143091305041347219672357065)
        ·
          refine ⟨107318478781010414754267799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143091305041347219672357065 107318478781010414754267799)
          ·
            refine ⟨160977718171515622131401699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107318478781010414754267799 160977718171515622131401699)
            ·
              refine ⟨241466577257273433197102549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160977718171515622131401699 241466577257273433197102549)
              ·
                refine ⟨5659372904467346090557091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 241466577257273433197102549 5659372904467346090557091)
                ·
                  refine ⟨8489059356701019135835637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5659372904467346090557091 8489059356701019135835637)
                  ·
                    refine ⟨795849314690720543984591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8489059356701019135835637 795849314690720543984591)
                    ·
                      rfl

theorem cell23_4649733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 7, 1, 5].length) (baseStart_4649733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4649733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4649733 prefixEnd_4649733 := by exact prefixLift 4649733
  have htrace : WordTrace (prefixWord ++ tailWord_4649733) baseStart_4649733 baseEnd_4649733 := by
    simpa [prefixWord, tailWord_4649733, baseEnd_4649733] using wordTrace_append hprefix tailTrace_4649733
  have hstable : (prefixWord ++ tailWord_4649733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4649733).length < 2 ^ (prefixWord ++ tailWord_4649733).sum := by decide
  have hdescent : baseEnd_4649733 < baseStart_4649733 := by decide
  rcases family_descends (prefixWord ++ tailWord_4649733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4649747 : List Nat := [1, 1, 1, 2, 1, 3, 5, 4, 1, 1, 3]
def baseStart_4649747 : Nat := 118140960795 + 4649747 * 2 ^ 59
def prefixEnd_4649747 : Nat := 4983230072969 + 3 ^ 40 * 4649747 * 2
def baseEnd_4649747 : Nat := 2387555132801324577178709

theorem tailTrace_4649747 : CollatzResearch.WordTrace tailWord_4649747 prefixEnd_4649747 2387555132801324577178709 := by
  unfold tailWord_4649747
  simp only [CollatzResearch.WordTrace]
  refine ⟨169590205485768207410099495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113060136990512138273399663 169590205485768207410099495)
  ·
    refine ⟨254385308228652311115149243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169590205485768207410099495 254385308228652311115149243)
    ·
      refine ⟨381577962342978466672723865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254385308228652311115149243 381577962342978466672723865)
      ·
        refine ⟨286183471757233850004542899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 381577962342978466672723865 286183471757233850004542899)
        ·
          refine ⟨429275207635850775006814349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 286183471757233850004542899 429275207635850775006814349)
          ·
            refine ⟨160978202863444040627555381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 429275207635850775006814349 160978202863444040627555381)
            ·
              refine ⟨15091706518447878808833317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 160978202863444040627555381 15091706518447878808833317)
              ·
                refine ⟨2829694972208977276656247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15091706518447878808833317 2829694972208977276656247)
                ·
                  refine ⟨4244542458313465914984371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2829694972208977276656247 4244542458313465914984371)
                  ·
                    refine ⟨6366813687470198872476557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4244542458313465914984371 6366813687470198872476557)
                    ·
                      refine ⟨2387555132801324577178709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6366813687470198872476557 2387555132801324577178709)
                      ·
                        rfl

theorem cell23_4649747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 4, 1, 1, 3].length) (baseStart_4649747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4649747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4649747 prefixEnd_4649747 := by exact prefixLift 4649747
  have htrace : WordTrace (prefixWord ++ tailWord_4649747) baseStart_4649747 baseEnd_4649747 := by
    simpa [prefixWord, tailWord_4649747, baseEnd_4649747] using wordTrace_append hprefix tailTrace_4649747
  have hstable : (prefixWord ++ tailWord_4649747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4649747).length < 2 ^ (prefixWord ++ tailWord_4649747).sum := by decide
  have hdescent : baseEnd_4649747 < baseStart_4649747 := by decide
  rcases family_descends (prefixWord ++ tailWord_4649747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4649763 : List Nat := [1, 1, 1, 4, 2, 1, 1, 2, 6, 4]
def baseStart_4649763 : Nat := 118140960795 + 4649763 * 2 ^ 59
def prefixEnd_4649763 : Nat := 4983230072969 + 3 ^ 40 * 4649763 * 2
def baseEnd_4649763 : Nat := 795854449497265504859545

theorem tailTrace_4649763 : CollatzResearch.WordTrace tailWord_4649763 prefixEnd_4649763 795854449497265504859545 := by
  unfold tailWord_4649763
  simp only [CollatzResearch.WordTrace]
  refine ⟨169590789053710242142681943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113060526035806828095121295 169590789053710242142681943)
  ·
    refine ⟨254386183580565363214022915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169590789053710242142681943 254386183580565363214022915)
    ·
      refine ⟨381579275370848044821034373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254386183580565363214022915 381579275370848044821034373)
      ·
        refine ⟨71546114132034008403943945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 381579275370848044821034373 71546114132034008403943945)
        ·
          refine ⟨53659585599025506302957959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71546114132034008403943945 53659585599025506302957959)
          ·
            refine ⟨80489378398538259454436939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53659585599025506302957959 80489378398538259454436939)
            ·
              refine ⟨120734067597807389181655409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80489378398538259454436939 120734067597807389181655409)
              ·
                refine ⟨90550550698355541886241557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 120734067597807389181655409 90550550698355541886241557)
                ·
                  refine ⟨4244557063985416025917573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 90550550698355541886241557 4244557063985416025917573)
                  ·
                    refine ⟨795854449497265504859545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4244557063985416025917573 795854449497265504859545)
                    ·
                      rfl

theorem cell23_4649763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 6, 4].length) (baseStart_4649763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4649763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4649763 prefixEnd_4649763 := by exact prefixLift 4649763
  have htrace : WordTrace (prefixWord ++ tailWord_4649763) baseStart_4649763 baseEnd_4649763 := by
    simpa [prefixWord, tailWord_4649763, baseEnd_4649763] using wordTrace_append hprefix tailTrace_4649763
  have hstable : (prefixWord ++ tailWord_4649763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4649763).length < 2 ^ (prefixWord ++ tailWord_4649763).sum := by decide
  have hdescent : baseEnd_4649763 < baseStart_4649763 := by decide
  rcases family_descends (prefixWord ++ tailWord_4649763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4649774 : List Nat := [4, 1, 3, 2, 1, 1, 3, 1, 2, 3, 2]
def baseStart_4649774 : Nat := 118140960795 + 4649774 * 2 ^ 59
def prefixEnd_4649774 : Nat := 4983230072969 + 3 ^ 40 * 4649774 * 2
def baseEnd_4649774 : Nat := 2387568996778995971541085

theorem tailTrace_4649774 : CollatzResearch.WordTrace tailWord_4649774 prefixEnd_4649774 2387568996778995971541085 := by
  unfold tailWord_4649774
  simp only [CollatzResearch.WordTrace]
  refine ⟨21198898782083798877666547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113060793504446927347554917 21198898782083798877666547)
  ·
    refine ⟨31798348173125698316499821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21198898782083798877666547 31798348173125698316499821)
    ·
      refine ⟨11924380564922136868687433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31798348173125698316499821 11924380564922136868687433)
      ·
        refine ⟨8943285423691602651515575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11924380564922136868687433 8943285423691602651515575)
        ·
          refine ⟨13414928135537403977273363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8943285423691602651515575 13414928135537403977273363)
          ·
            refine ⟨20122392203306105965910045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13414928135537403977273363 20122392203306105965910045)
            ·
              refine ⟨7545897076239789737216267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20122392203306105965910045 7545897076239789737216267)
              ·
                refine ⟨11318845614359684605824401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7545897076239789737216267 11318845614359684605824401)
                ·
                  refine ⟨8489134210769763454368301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11318845614359684605824401 8489134210769763454368301)
                  ·
                    refine ⟨3183425329038661295388113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8489134210769763454368301 3183425329038661295388113)
                    ·
                      refine ⟨2387568996778995971541085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3183425329038661295388113 2387568996778995971541085)
                      ·
                        rfl

theorem cell23_4649774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_4649774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4649774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4649774 prefixEnd_4649774 := by exact prefixLift 4649774
  have htrace : WordTrace (prefixWord ++ tailWord_4649774) baseStart_4649774 baseEnd_4649774 := by
    simpa [prefixWord, tailWord_4649774, baseEnd_4649774] using wordTrace_append hprefix tailTrace_4649774
  have hstable : (prefixWord ++ tailWord_4649774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4649774).length < 2 ^ (prefixWord ++ tailWord_4649774).sum := by decide
  have hdescent : baseEnd_4649774 < baseStart_4649774 := by decide
  rcases family_descends (prefixWord ++ tailWord_4649774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4649776 : List Nat := [2, 1, 1, 1, 2, 2, 1, 13]
def baseStart_4649776 : Nat := 118140960795 + 4649776 * 2 ^ 59
def prefixEnd_4649776 : Nat := 4983230072969 + 3 ^ 40 * 4649776 * 2
def baseEnd_4649776 : Nat := 88428519397789072730225

theorem tailTrace_4649776 : CollatzResearch.WordTrace tailWord_4649776 prefixEnd_4649776 88428519397789072730225 := by
  unfold tailWord_4649776
  simp only [CollatzResearch.WordTrace]
  refine ⟨84795631601331572681452591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113060842135108763575270121 84795631601331572681452591)
  ·
    refine ⟨127193447401997359022178887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84795631601331572681452591 127193447401997359022178887)
    ·
      refine ⟨190790171102996038533268331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127193447401997359022178887 190790171102996038533268331)
      ·
        refine ⟨286185256654494057799902497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190790171102996038533268331 286185256654494057799902497)
        ·
          refine ⟨214638942490870543349926873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 286185256654494057799902497 214638942490870543349926873)
          ·
            refine ⟨160979206868152907512445155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 214638942490870543349926873 160979206868152907512445155)
            ·
              refine ⟨241468810302229361268667733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160979206868152907512445155 241468810302229361268667733)
              ·
                refine ⟨88428519397789072730225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 241468810302229361268667733 88428519397789072730225)
                ·
                  rfl

theorem cell23_4649776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 13].length) (baseStart_4649776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4649776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4649776 prefixEnd_4649776 := by exact prefixLift 4649776
  have htrace : WordTrace (prefixWord ++ tailWord_4649776) baseStart_4649776 baseEnd_4649776 := by
    simpa [prefixWord, tailWord_4649776, baseEnd_4649776] using wordTrace_append hprefix tailTrace_4649776
  have hstable : (prefixWord ++ tailWord_4649776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4649776).length < 2 ^ (prefixWord ++ tailWord_4649776).sum := by decide
  have hdescent : baseEnd_4649776 < baseStart_4649776 := by decide
  rcases family_descends (prefixWord ++ tailWord_4649776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4649783 : List Nat := [1, 1, 3, 1, 2, 1, 3, 4, 1, 2, 4]
def baseStart_4649783 : Nat := 118140960795 + 4649783 * 2 ^ 59
def prefixEnd_4649783 : Nat := 4983230072969 + 3 ^ 40 * 4649783 * 2
def baseEnd_4649783 : Nat := 2387573618104886436328543

theorem tailTrace_4649783 : CollatzResearch.WordTrace tailWord_4649783 prefixEnd_4649783 2387573618104886436328543 := by
  unfold tailWord_4649783
  simp only [CollatzResearch.WordTrace]
  refine ⟨169591518513637785558410003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113061012342425190372273335 169591518513637785558410003)
  ·
    refine ⟨254387277770456678337615005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169591518513637785558410003 254387277770456678337615005)
    ·
      refine ⟨95395229163921254376605627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 254387277770456678337615005 95395229163921254376605627)
      ·
        refine ⟨143092843745881881564908441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95395229163921254376605627 143092843745881881564908441)
        ·
          refine ⟨107319632809411411173681331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143092843745881881564908441 107319632809411411173681331)
          ·
            refine ⟨160979449214117116760521997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107319632809411411173681331 160979449214117116760521997)
            ·
              refine ⟨60367293455293918785195749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 160979449214117116760521997 60367293455293918785195749)
              ·
                refine ⟨11318867522867609772224203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60367293455293918785195749 11318867522867609772224203)
                ·
                  refine ⟨16978301284301414658336305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11318867522867609772224203 16978301284301414658336305)
                  ·
                    refine ⟨12733725963226060993752229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16978301284301414658336305 12733725963226060993752229)
                    ·
                      refine ⟨2387573618104886436328543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12733725963226060993752229 2387573618104886436328543)
                      ·
                        rfl

theorem cell23_4649783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 4, 1, 2, 4].length) (baseStart_4649783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4649783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4649783 prefixEnd_4649783 := by exact prefixLift 4649783
  have htrace : WordTrace (prefixWord ++ tailWord_4649783) baseStart_4649783 baseEnd_4649783 := by
    simpa [prefixWord, tailWord_4649783, baseEnd_4649783] using wordTrace_append hprefix tailTrace_4649783
  have hstable : (prefixWord ++ tailWord_4649783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4649783).length < 2 ^ (prefixWord ++ tailWord_4649783).sum := by decide
  have hdescent : baseEnd_4649783 < baseStart_4649783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4649783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4649804 : List Nat := [2, 2, 1, 3, 3, 2, 2, 1, 3, 2, 2]
def baseStart_4649804 : Nat := 118140960795 + 4649804 * 2 ^ 59
def prefixEnd_4649804 : Nat := 4983230072969 + 3 ^ 40 * 4649804 * 2
def baseEnd_4649804 : Nat := 2387584401198630854165947

theorem tailTrace_4649804 : CollatzResearch.WordTrace tailWord_4649804 prefixEnd_4649804 2387584401198630854165947 := by
  unfold tailWord_4649804
  simp only [CollatzResearch.WordTrace]
  refine ⟨84796142223280853072462233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113061522964374470763282977 84796142223280853072462233)
  ·
    refine ⟨63597106667460639804346675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84796142223280853072462233 63597106667460639804346675)
    ·
      refine ⟨95395660001190959706520013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63597106667460639804346675 95395660001190959706520013)
      ·
        refine ⟨35773372500446609889945005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95395660001190959706520013 35773372500446609889945005)
        ·
          refine ⟨13415014687667478708729377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35773372500446609889945005 13415014687667478708729377)
          ·
            refine ⟨10061261015750609031547033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13415014687667478708729377 10061261015750609031547033)
            ·
              refine ⟨7545945761812956773660275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10061261015750609031547033 7545945761812956773660275)
              ·
                refine ⟨11318918642719435160490413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7545945761812956773660275 11318918642719435160490413)
                ·
                  refine ⟨4244594491019788185183905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11318918642719435160490413 4244594491019788185183905)
                  ·
                    refine ⟨3183445868264841138887929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4244594491019788185183905 3183445868264841138887929)
                    ·
                      refine ⟨2387584401198630854165947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3183445868264841138887929 2387584401198630854165947)
                      ·
                        rfl

theorem cell23_4649804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 1, 3, 2, 2].length) (baseStart_4649804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4649804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4649804 prefixEnd_4649804 := by exact prefixLift 4649804
  have htrace : WordTrace (prefixWord ++ tailWord_4649804) baseStart_4649804 baseEnd_4649804 := by
    simpa [prefixWord, tailWord_4649804, baseEnd_4649804] using wordTrace_append hprefix tailTrace_4649804
  have hstable : (prefixWord ++ tailWord_4649804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4649804).length < 2 ^ (prefixWord ++ tailWord_4649804).sum := by decide
  have hdescent : baseEnd_4649804 < baseStart_4649804 := by decide
  rcases family_descends (prefixWord ++ tailWord_4649804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4649853 : List Nat := [1, 4, 1, 1, 2, 1, 2, 1, 4, 6]
def baseStart_4649853 : Nat := 118140960795 + 4649853 * 2 ^ 59
def prefixEnd_4649853 : Nat := 4983230072969 + 3 ^ 40 * 4649853 * 2
def baseEnd_4649853 : Nat := 795869853916900387484407

theorem tailTrace_4649853 : CollatzResearch.WordTrace tailWord_4649853 prefixEnd_4649853 795869853916900387484407 := by
  unfold tailWord_4649853
  simp only [CollatzResearch.WordTrace]
  refine ⟨169594071623384187513458213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113062714415589458342305475 169594071623384187513458213)
  ·
    refine ⟨31798888429384535158773415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 169594071623384187513458213 31798888429384535158773415)
    ·
      refine ⟨47698332644076802738160123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31798888429384535158773415 47698332644076802738160123)
      ·
        refine ⟨71547498966115204107240185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47698332644076802738160123 71547498966115204107240185)
        ·
          refine ⟨53660624224586403080430139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71547498966115204107240185 53660624224586403080430139)
          ·
            refine ⟨80490936336879604620645209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53660624224586403080430139 80490936336879604620645209)
            ·
              refine ⟨60368202252659703465483907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80490936336879604620645209 60368202252659703465483907)
              ·
                refine ⟨90552303378989555198225861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60368202252659703465483907 90552303378989555198225861)
                ·
                  refine ⟨16978556883560541599667349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 90552303378989555198225861 16978556883560541599667349)
                  ·
                    refine ⟨795869853916900387484407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16978556883560541599667349 795869853916900387484407)
                    ·
                      rfl

theorem cell23_4649853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 4, 6].length) (baseStart_4649853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4649853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4649853 prefixEnd_4649853 := by exact prefixLift 4649853
  have htrace : WordTrace (prefixWord ++ tailWord_4649853) baseStart_4649853 baseEnd_4649853 := by
    simpa [prefixWord, tailWord_4649853, baseEnd_4649853] using wordTrace_append hprefix tailTrace_4649853
  have hstable : (prefixWord ++ tailWord_4649853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4649853).length < 2 ^ (prefixWord ++ tailWord_4649853).sum := by decide
  have hdescent : baseEnd_4649853 < baseStart_4649853 := by decide
  rcases family_descends (prefixWord ++ tailWord_4649853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4649873 : List Nat := [1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 4]
def baseStart_4649873 : Nat := 118140960795 + 4649873 * 2 ^ 59
def prefixEnd_4649873 : Nat := 4983230072969 + 3 ^ 40 * 4649873 * 2
def baseEnd_4649873 : Nat := 2387619831363791084203129

theorem tailTrace_4649873 : CollatzResearch.WordTrace tailWord_4649873 prefixEnd_4649873 2387619831363791084203129 := by
  unfold tailWord_4649873
  simp only [CollatzResearch.WordTrace]
  refine ⟨169594801083311730929186273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113063200722207820619457515 169594801083311730929186273)
  ·
    refine ⟨127196100812483798196889705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169594801083311730929186273 127196100812483798196889705)
    ·
      refine ⟨95397075609362848647667279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127196100812483798196889705 95397075609362848647667279)
      ·
        refine ⟨143095613414044272971500919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95397075609362848647667279 143095613414044272971500919)
        ·
          refine ⟨214643420121066409457251379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143095613414044272971500919 214643420121066409457251379)
          ·
            refine ⟨321965130181599614185877069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214643420121066409457251379 321965130181599614185877069)
            ·
              refine ⟨120736923818099855319703901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 321965130181599614185877069 120736923818099855319703901)
              ·
                refine ⟨45276346431787445744888963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120736923818099855319703901 45276346431787445744888963)
                ·
                  refine ⟨67914519647681168617333445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45276346431787445744888963 67914519647681168617333445)
                  ·
                    refine ⟨12733972433940219115750021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 67914519647681168617333445 12733972433940219115750021)
                    ·
                      refine ⟨2387619831363791084203129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12733972433940219115750021 2387619831363791084203129)
                      ·
                        rfl

theorem cell23_4649873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 4].length) (baseStart_4649873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4649873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4649873 prefixEnd_4649873 := by exact prefixLift 4649873
  have htrace : WordTrace (prefixWord ++ tailWord_4649873) baseStart_4649873 baseEnd_4649873 := by
    simpa [prefixWord, tailWord_4649873, baseEnd_4649873] using wordTrace_append hprefix tailTrace_4649873
  have hstable : (prefixWord ++ tailWord_4649873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4649873).length < 2 ^ (prefixWord ++ tailWord_4649873).sum := by decide
  have hdescent : baseEnd_4649873 < baseStart_4649873 := by decide
  rcases family_descends (prefixWord ++ tailWord_4649873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4649924 : List Nat := [2, 3, 3, 3, 1, 1, 1, 1, 2, 2, 4]
def baseStart_4649924 : Nat := 118140960795 + 4649924 * 2 ^ 59
def prefixEnd_4649924 : Nat := 4983230072969 + 3 ^ 40 * 4649924 * 2
def baseEnd_4649924 : Nat := 2387646018877170384665395

theorem tailTrace_4649924 : CollatzResearch.WordTrace tailWord_4649924 prefixEnd_4649924 2387646018877170384665395 := by
  unfold tailWord_4649924
  simp only [CollatzResearch.WordTrace]
  refine ⟨84798330603063483319646413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113064440804084644426195217 84798330603063483319646413)
  ·
    refine ⟨31799373976148806244867405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84798330603063483319646413 31799373976148806244867405)
    ·
      refine ⟨11924765241055802341825277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31799373976148806244867405 11924765241055802341825277)
      ·
        refine ⟨4471786965395925878184479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11924765241055802341825277 4471786965395925878184479)
        ·
          refine ⟨6707680448093888817276719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4471786965395925878184479 6707680448093888817276719)
          ·
            refine ⟨10061520672140833225915079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6707680448093888817276719 10061520672140833225915079)
            ·
              refine ⟨15092281008211249838872619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10061520672140833225915079 15092281008211249838872619)
              ·
                refine ⟨22638421512316874758308929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15092281008211249838872619 22638421512316874758308929)
                ·
                  refine ⟨16978816134237656068731697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22638421512316874758308929 16978816134237656068731697)
                  ·
                    refine ⟨12734112100678242051548773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16978816134237656068731697 12734112100678242051548773)
                    ·
                      refine ⟨2387646018877170384665395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12734112100678242051548773 2387646018877170384665395)
                      ·
                        rfl

theorem cell23_4649924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_4649924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4649924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4649924 prefixEnd_4649924 := by exact prefixLift 4649924
  have htrace : WordTrace (prefixWord ++ tailWord_4649924) baseStart_4649924 baseEnd_4649924 := by
    simpa [prefixWord, tailWord_4649924, baseEnd_4649924] using wordTrace_append hprefix tailTrace_4649924
  have hstable : (prefixWord ++ tailWord_4649924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4649924).length < 2 ^ (prefixWord ++ tailWord_4649924).sum := by decide
  have hdescent : baseEnd_4649924 < baseStart_4649924 := by decide
  rcases family_descends (prefixWord ++ tailWord_4649924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4649943 : List Nat := [1, 1, 3, 2, 1, 1, 2, 1, 1, 10]
def baseStart_4649943 : Nat := 118140960795 + 4649943 * 2 ^ 59
def prefixEnd_4649943 : Nat := 4983230072969 + 3 ^ 40 * 4649943 * 2
def baseEnd_4649943 : Nat := 795885258336535270109269

theorem tailTrace_4649943 : CollatzResearch.WordTrace tailWord_4649943 prefixEnd_4649943 795885258336535270109269 := by
  unfold tailWord_4649943
  simp only [CollatzResearch.WordTrace]
  refine ⟨169597354193058132884234483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113064902795372088589489655 169597354193058132884234483)
  ·
    refine ⟨254396031289587199326351725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169597354193058132884234483 254396031289587199326351725)
    ·
      refine ⟨95398511733595199747381897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 254396031289587199326351725 95398511733595199747381897)
      ·
        refine ⟨71548883800196399810536423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95398511733595199747381897 71548883800196399810536423)
        ·
          refine ⟨107323325700294599715804635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71548883800196399810536423 107323325700294599715804635)
          ·
            refine ⟨160984988550441899573706953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107323325700294599715804635 160984988550441899573706953)
            ·
              refine ⟨120738741412831424680280215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 160984988550441899573706953 120738741412831424680280215)
              ·
                refine ⟨181108112119247137020420323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120738741412831424680280215 181108112119247137020420323)
                ·
                  refine ⟨271662168178870705530630485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 181108112119247137020420323 271662168178870705530630485)
                  ·
                    refine ⟨795885258336535270109269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 271662168178870705530630485 795885258336535270109269)
                    ·
                      rfl

theorem cell23_4649943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 10].length) (baseStart_4649943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4649943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4649943 prefixEnd_4649943 := by exact prefixLift 4649943
  have htrace : WordTrace (prefixWord ++ tailWord_4649943) baseStart_4649943 baseEnd_4649943 := by
    simpa [prefixWord, tailWord_4649943, baseEnd_4649943] using wordTrace_append hprefix tailTrace_4649943
  have hstable : (prefixWord ++ tailWord_4649943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4649943).length < 2 ^ (prefixWord ++ tailWord_4649943).sum := by decide
  have hdescent : baseEnd_4649943 < baseStart_4649943 := by decide
  rcases family_descends (prefixWord ++ tailWord_4649943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4649967 : List Nat := [1, 1, 2, 1, 4, 3, 1, 2, 2, 4, 2]
def baseStart_4649967 : Nat := 118140960795 + 4649967 * 2 ^ 59
def prefixEnd_4649967 : Nat := 4983230072969 + 3 ^ 40 * 4649967 * 2
def baseEnd_4649967 : Nat := 2387668098545313716427697

theorem tailTrace_4649967 : CollatzResearch.WordTrace tailWord_4649967 prefixEnd_4649967 2387668098545313716427697 := by
  unfold tailWord_4649967
  simp only [CollatzResearch.WordTrace]
  refine ⟨169598229544971184983108155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113065486363314123322072103 169598229544971184983108155)
  ·
    refine ⟨254397344317456777474662233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169598229544971184983108155 254397344317456777474662233)
    ·
      refine ⟨190798008238092583105996675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 254397344317456777474662233 190798008238092583105996675)
      ·
        refine ⟨286197012357138874658995013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190798008238092583105996675 286197012357138874658995013)
        ·
          refine ⟨53661939816963538998561565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 286197012357138874658995013 53661939816963538998561565)
          ·
            refine ⟨20123227431361327124460587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53661939816963538998561565 20123227431361327124460587)
            ·
              refine ⟨30184841147041990686690881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20123227431361327124460587 30184841147041990686690881)
              ·
                refine ⟨22638630860281493015018161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30184841147041990686690881 22638630860281493015018161)
                ·
                  refine ⟨16978973145211119761263621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22638630860281493015018161 16978973145211119761263621)
                  ·
                    refine ⟨3183557464727084955236929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16978973145211119761263621 3183557464727084955236929)
                    ·
                      refine ⟨2387668098545313716427697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3183557464727084955236929 2387668098545313716427697)
                      ·
                        rfl

theorem cell23_4649967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 2, 4, 2].length) (baseStart_4649967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4649967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4649967 prefixEnd_4649967 := by exact prefixLift 4649967
  have htrace : WordTrace (prefixWord ++ tailWord_4649967) baseStart_4649967 baseEnd_4649967 := by
    simpa [prefixWord, tailWord_4649967, baseEnd_4649967] using wordTrace_append hprefix tailTrace_4649967
  have hstable : (prefixWord ++ tailWord_4649967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4649967).length < 2 ^ (prefixWord ++ tailWord_4649967).sum := by decide
  have hdescent : baseEnd_4649967 < baseStart_4649967 := by decide
  rcases family_descends (prefixWord ++ tailWord_4649967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4649977 : List Nat := [1, 2, 1, 3, 1, 3, 4, 1, 3, 4]
def baseStart_4649977 : Nat := 118140960795 + 4649977 * 2 ^ 59
def prefixEnd_4649977 : Nat := 4983230072969 + 3 ^ 40 * 4649977 * 2
def baseEnd_4649977 : Nat := 795891077783952892434217

theorem tailTrace_4649977 : CollatzResearch.WordTrace tailWord_4649977 prefixEnd_4649977 795891077783952892434217 := by
  unfold tailWord_4649977
  simp only [CollatzResearch.WordTrace]
  refine ⟨169598594274934956690972185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113065729516623304460648123 169598594274934956690972185)
  ·
    refine ⟨127198945706201217518229139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169598594274934956690972185 127198945706201217518229139)
    ·
      refine ⟨190798418559301826277343709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127198945706201217518229139 190798418559301826277343709)
      ·
        refine ⟨71549406959738184854003891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 190798418559301826277343709 71549406959738184854003891)
        ·
          refine ⟨107324110439607277281005837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71549406959738184854003891 107324110439607277281005837)
          ·
            refine ⟨40246541414852728980377189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107324110439607277281005837 40246541414852728980377189)
            ·
              refine ⟨7546226515284886683820723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40246541414852728980377189 7546226515284886683820723)
              ·
                refine ⟨11319339772927330025731085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7546226515284886683820723 11319339772927330025731085)
                ·
                  refine ⟨4244752414847748759649157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11319339772927330025731085 4244752414847748759649157)
                  ·
                    refine ⟨795891077783952892434217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4244752414847748759649157 795891077783952892434217)
                    ·
                      rfl

theorem cell23_4649977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 1, 3, 4].length) (baseStart_4649977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4649977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4649977 prefixEnd_4649977 := by exact prefixLift 4649977
  have htrace : WordTrace (prefixWord ++ tailWord_4649977) baseStart_4649977 baseEnd_4649977 := by
    simpa [prefixWord, tailWord_4649977, baseEnd_4649977] using wordTrace_append hprefix tailTrace_4649977
  have hstable : (prefixWord ++ tailWord_4649977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4649977).length < 2 ^ (prefixWord ++ tailWord_4649977).sum := by decide
  have hdescent : baseEnd_4649977 < baseStart_4649977 := by decide
  rcases family_descends (prefixWord ++ tailWord_4649977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4650057 : List Nat := [1, 2, 1, 1, 2, 2, 2, 6, 1, 1, 4]
def baseStart_4650057 : Nat := 118140960795 + 4650057 * 2 ^ 59
def prefixEnd_4650057 : Nat := 4983230072969 + 3 ^ 40 * 4650057 * 2
def baseEnd_4650057 : Nat := 2387714311804218364302283

theorem tailTrace_4650057 : CollatzResearch.WordTrace tailWord_4650057 prefixEnd_4650057 2387714311804218364302283 := by
  unfold tailWord_4650057
  simp only [CollatzResearch.WordTrace]
  refine ⟨169601512114645130353884425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113067674743096753569256283 169601512114645130353884425)
  ·
    refine ⟨127201134085983847765413319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169601512114645130353884425 127201134085983847765413319)
    ·
      refine ⟨190801701128975771648119979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127201134085983847765413319 190801701128975771648119979)
      ·
        refine ⟨286202551693463657472179969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190801701128975771648119979 286202551693463657472179969)
        ·
          refine ⟨214651913770097743104134977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 286202551693463657472179969 214651913770097743104134977)
          ·
            refine ⟨160988935327573307328101233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 214651913770097743104134977 160988935327573307328101233)
            ·
              refine ⟨120741701495679980496075925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 160988935327573307328101233 120741701495679980496075925)
              ·
                refine ⟨5659767257609999085753559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 120741701495679980496075925 5659767257609999085753559)
                ·
                  refine ⟨8489650886414998628630339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5659767257609999085753559 8489650886414998628630339)
                  ·
                    refine ⟨12734476329622497942945509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8489650886414998628630339 12734476329622497942945509)
                    ·
                      refine ⟨2387714311804218364302283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12734476329622497942945509 2387714311804218364302283)
                      ·
                        rfl

theorem cell23_4650057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 6, 1, 1, 4].length) (baseStart_4650057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4650057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4650057 prefixEnd_4650057 := by exact prefixLift 4650057
  have htrace : WordTrace (prefixWord ++ tailWord_4650057) baseStart_4650057 baseEnd_4650057 := by
    simpa [prefixWord, tailWord_4650057, baseEnd_4650057] using wordTrace_append hprefix tailTrace_4650057
  have hstable : (prefixWord ++ tailWord_4650057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4650057).length < 2 ^ (prefixWord ++ tailWord_4650057).sum := by decide
  have hdescent : baseEnd_4650057 < baseStart_4650057 := by decide
  rcases family_descends (prefixWord ++ tailWord_4650057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4650061 : List Nat := [1, 6, 1, 1, 1, 2, 1, 3, 2, 3, 2]
def baseStart_4650061 : Nat := 118140960795 + 4650061 * 2 ^ 59
def prefixEnd_4650061 : Nat := 4983230072969 + 3 ^ 40 * 4650061 * 2
def baseEnd_4650061 : Nat := 2387716365726836348652265

theorem tailTrace_4650061 : CollatzResearch.WordTrace tailWord_4650061 prefixEnd_4650061 2387716365726836348652265 := by
  unfold tailWord_4650061
  simp only [CollatzResearch.WordTrace]
  refine ⟨169601658006630639037030037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113067772004420426024686691 169601658006630639037030037)
  ·
    refine ⟨7950077719060811204860783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 169601658006630639037030037 7950077719060811204860783)
    ·
      refine ⟨11925116578591216807291175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7950077719060811204860783 11925116578591216807291175)
      ·
        refine ⟨17887674867886825210936763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11925116578591216807291175 17887674867886825210936763)
        ·
          refine ⟨26831512301830237816405145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17887674867886825210936763 26831512301830237816405145)
          ·
            refine ⟨20123634226372678362303859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26831512301830237816405145 20123634226372678362303859)
            ·
              refine ⟨30185451339559017543455789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20123634226372678362303859 30185451339559017543455789)
              ·
                refine ⟨11319544252334631578795921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30185451339559017543455789 11319544252334631578795921)
                ·
                  refine ⟨8489658189250973684096941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11319544252334631578795921 8489658189250973684096941)
                  ·
                    refine ⟨3183621820969115131536353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8489658189250973684096941 3183621820969115131536353)
                    ·
                      refine ⟨2387716365726836348652265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3183621820969115131536353 2387716365726836348652265)
                      ·
                        rfl

theorem cell23_4650061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 3, 2, 3, 2].length) (baseStart_4650061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4650061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4650061 prefixEnd_4650061 := by exact prefixLift 4650061
  have htrace : WordTrace (prefixWord ++ tailWord_4650061) baseStart_4650061 baseEnd_4650061 := by
    simpa [prefixWord, tailWord_4650061, baseEnd_4650061] using wordTrace_append hprefix tailTrace_4650061
  have hstable : (prefixWord ++ tailWord_4650061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4650061).length < 2 ^ (prefixWord ++ tailWord_4650061).sum := by decide
  have hdescent : baseEnd_4650061 < baseStart_4650061 := by decide
  rcases family_descends (prefixWord ++ tailWord_4650061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4650074 : List Nat := [3, 1, 1, 2, 1, 1, 2, 1, 7, 2, 2]
def baseStart_4650074 : Nat := 118140960795 + 4650074 * 2 ^ 59
def prefixEnd_4650074 : Nat := 4983230072969 + 3 ^ 40 * 4650074 * 2
def baseEnd_4650074 : Nat := 2387723040975344797789705

theorem tailTrace_4650074 : CollatzResearch.WordTrace tailWord_4650074 prefixEnd_4650074 2387723040975344797789705 := by
  unfold tailWord_4650074
  simp only [CollatzResearch.WordTrace]
  refine ⟨42400533038895885564313319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113068088103722361504835517 42400533038895885564313319)
  ·
    refine ⟨63600799558343828346469979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42400533038895885564313319 63600799558343828346469979)
    ·
      refine ⟨95401199337515742519704969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63600799558343828346469979 95401199337515742519704969)
      ·
        refine ⟨71550899503136806889778727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95401199337515742519704969 71550899503136806889778727)
        ·
          refine ⟨107326349254705210334668091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71550899503136806889778727 107326349254705210334668091)
          ·
            refine ⟨160989523882057815502002137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107326349254705210334668091 160989523882057815502002137)
            ·
              refine ⟨120742142911543361626501603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 160989523882057815502002137 120742142911543361626501603)
              ·
                refine ⟨181113214367315042439752405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120742142911543361626501603 181113214367315042439752405)
                ·
                  refine ⟨4244840961733946307181697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 181113214367315042439752405 4244840961733946307181697)
                  ·
                    refine ⟨3183630721300459730386273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4244840961733946307181697 3183630721300459730386273)
                    ·
                      refine ⟨2387723040975344797789705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3183630721300459730386273 2387723040975344797789705)
                      ·
                        rfl

theorem cell23_4650074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 7, 2, 2].length) (baseStart_4650074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4650074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4650074 prefixEnd_4650074 := by exact prefixLift 4650074
  have htrace : WordTrace (prefixWord ++ tailWord_4650074) baseStart_4650074 baseEnd_4650074 := by
    simpa [prefixWord, tailWord_4650074, baseEnd_4650074] using wordTrace_append hprefix tailTrace_4650074
  have hstable : (prefixWord ++ tailWord_4650074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4650074).length < 2 ^ (prefixWord ++ tailWord_4650074).sum := by decide
  have hdescent : baseEnd_4650074 < baseStart_4650074 := by decide
  rcases family_descends (prefixWord ++ tailWord_4650074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4650094 : List Nat := [4, 1, 2, 2, 1, 2, 1, 2, 3, 2, 3]
def baseStart_4650094 : Nat := 118140960795 + 4650094 * 2 ^ 59
def prefixEnd_4650094 : Nat := 4983230072969 + 3 ^ 40 * 4650094 * 2
def baseEnd_4650094 : Nat := 2387733310588434719539613

theorem tailTrace_4650094 : CollatzResearch.WordTrace tailWord_4650094 prefixEnd_4650094 2387733310588434719539613 := by
  unfold tailWord_4650094
  simp only [CollatzResearch.WordTrace]
  refine ⟨21200357701938885709122667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113068574410340723781987557 21200357701938885709122667)
  ·
    refine ⟨31800536552908328563684001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21200357701938885709122667 31800536552908328563684001)
    ·
      refine ⟨23850402414681246422763001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31800536552908328563684001 23850402414681246422763001)
      ·
        refine ⟨17887801811010934817072251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23850402414681246422763001 17887801811010934817072251)
        ·
          refine ⟨26831702716516402225608377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17887801811010934817072251 26831702716516402225608377)
          ·
            refine ⟨20123777037387301669206283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26831702716516402225608377 20123777037387301669206283)
            ·
              refine ⟨30185665556080952503809425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20123777037387301669206283 30185665556080952503809425)
              ·
                refine ⟨22639249167060714377857069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30185665556080952503809425 22639249167060714377857069)
                ·
                  refine ⟨8489718437647767891696401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22639249167060714377857069 8489718437647767891696401)
                  ·
                    refine ⟨6367288828235825918772301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8489718437647767891696401 6367288828235825918772301)
                    ·
                      refine ⟨2387733310588434719539613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6367288828235825918772301 2387733310588434719539613)
                      ·
                        rfl

theorem cell23_4650094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_4650094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4650094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4650094 prefixEnd_4650094 := by exact prefixLift 4650094
  have htrace : WordTrace (prefixWord ++ tailWord_4650094) baseStart_4650094 baseEnd_4650094 := by
    simpa [prefixWord, tailWord_4650094, baseEnd_4650094] using wordTrace_append hprefix tailTrace_4650094
  have hstable : (prefixWord ++ tailWord_4650094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4650094).length < 2 ^ (prefixWord ++ tailWord_4650094).sum := by decide
  have hdescent : baseEnd_4650094 < baseStart_4650094 := by decide
  rcases family_descends (prefixWord ++ tailWord_4650094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4650101 : List Nat := [1, 3, 4, 3, 1, 1, 2, 1, 1, 6]
def baseStart_4650101 : Nat := 118140960795 + 4650101 * 2 ^ 59
def prefixEnd_4650101 : Nat := 4983230072969 + 3 ^ 40 * 4650101 * 2
def baseEnd_4650101 : Nat := 795912301651005397384027

theorem tailTrace_4650101 : CollatzResearch.WordTrace tailWord_4650101 prefixEnd_4650101 795912301651005397384027 := by
  unfold tailWord_4650101
  simp only [CollatzResearch.WordTrace]
  refine ⟨169603116926485725868486157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113068744617657150578990771 169603116926485725868486157)
  ·
    refine ⟨63601168847432147200682309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169603116926485725868486157 63601168847432147200682309)
    ·
      refine ⟨11925219158893527600127933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63601168847432147200682309 11925219158893527600127933)
      ·
        refine ⟨4471957184585072850047975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11925219158893527600127933 4471957184585072850047975)
        ·
          refine ⟨6707935776877609275071963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4471957184585072850047975 6707935776877609275071963)
          ·
            refine ⟨10061903665316413912607945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6707935776877609275071963 10061903665316413912607945)
            ·
              refine ⟨7546427748987310434455959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10061903665316413912607945 7546427748987310434455959)
              ·
                refine ⟨11319641623480965651683939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7546427748987310434455959 11319641623480965651683939)
                ·
                  refine ⟨16979462435221448477525909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11319641623480965651683939 16979462435221448477525909)
                  ·
                    refine ⟨795912301651005397384027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16979462435221448477525909 795912301651005397384027)
                    ·
                      rfl

theorem cell23_4650101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_4650101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4650101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4650101 prefixEnd_4650101 := by exact prefixLift 4650101
  have htrace : WordTrace (prefixWord ++ tailWord_4650101) baseStart_4650101 baseEnd_4650101 := by
    simpa [prefixWord, tailWord_4650101, baseEnd_4650101] using wordTrace_append hprefix tailTrace_4650101
  have hstable : (prefixWord ++ tailWord_4650101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4650101).length < 2 ^ (prefixWord ++ tailWord_4650101).sum := by decide
  have hdescent : baseEnd_4650101 < baseStart_4650101 := by decide
  rcases family_descends (prefixWord ++ tailWord_4650101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4650167 : List Nat := [1, 1, 3, 1, 4, 1, 2, 2, 2, 1, 5]
def baseStart_4650167 : Nat := 118140960795 + 4650167 * 2 ^ 59
def prefixEnd_4650167 : Nat := 4983230072969 + 3 ^ 40 * 4650167 * 2
def baseEnd_4650167 : Nat := 2387770794676212933926777

theorem tailTrace_4650167 : CollatzResearch.WordTrace tailWord_4650167 prefixEnd_4650167 2387770794676212933926777 := by
  unfold tailWord_4650167
  simp only [CollatzResearch.WordTrace]
  refine ⟨169605524144246619140388755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113070349429497746093592503 169605524144246619140388755)
  ·
    refine ⟨254408286216369928710583133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169605524144246619140388755 254408286216369928710583133)
    ·
      refine ⟨95403107331138723266468675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 254408286216369928710583133 95403107331138723266468675)
      ·
        refine ⟨143104660996708084899703013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95403107331138723266468675 143104660996708084899703013)
        ·
          refine ⟨26832123936882765918694315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 143104660996708084899703013 26832123936882765918694315)
          ·
            refine ⟨40248185905324148878041473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26832123936882765918694315 40248185905324148878041473)
            ·
              refine ⟨30186139428993111658531105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40248185905324148878041473 30186139428993111658531105)
              ·
                refine ⟨22639604571744833743898329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30186139428993111658531105 22639604571744833743898329)
                ·
                  refine ⟨16979703428808625307923747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22639604571744833743898329 16979703428808625307923747)
                  ·
                    refine ⟨25469555143212937961885621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16979703428808625307923747 25469555143212937961885621)
                    ·
                      refine ⟨2387770794676212933926777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25469555143212937961885621 2387770794676212933926777)
                      ·
                        rfl

theorem cell23_4650167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 2, 1, 5].length) (baseStart_4650167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4650167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4650167 prefixEnd_4650167 := by exact prefixLift 4650167
  have htrace : WordTrace (prefixWord ++ tailWord_4650167) baseStart_4650167 baseEnd_4650167 := by
    simpa [prefixWord, tailWord_4650167, baseEnd_4650167] using wordTrace_append hprefix tailTrace_4650167
  have hstable : (prefixWord ++ tailWord_4650167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4650167).length < 2 ^ (prefixWord ++ tailWord_4650167).sum := by decide
  have hdescent : baseEnd_4650167 < baseStart_4650167 := by decide
  rcases family_descends (prefixWord ++ tailWord_4650167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4650215 : List Nat := [1, 1, 5, 3, 2, 1, 1, 3, 2, 2, 2]
def baseStart_4650215 : Nat := 118140960795 + 4650215 * 2 ^ 59
def prefixEnd_4650215 : Nat := 4983230072969 + 3 ^ 40 * 4650215 * 2
def baseEnd_4650215 : Nat := 2387795441747628746126557

theorem tailTrace_4650215 : CollatzResearch.WordTrace tailWord_4650215 prefixEnd_4650215 2387795441747628746126557 := by
  unfold tailWord_4650215
  simp only [CollatzResearch.WordTrace]
  refine ⟨169607274848072723338136099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113071516565381815558757399 169607274848072723338136099)
  ·
    refine ⟨254410912272109085007204149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169607274848072723338136099 254410912272109085007204149)
    ·
      refine ⟨23851023025510226719425389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 254410912272109085007204149 23851023025510226719425389)
      ·
        refine ⟨8944133634566335019784521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23851023025510226719425389 8944133634566335019784521)
        ·
          refine ⟨6708100225924751264838391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8944133634566335019784521 6708100225924751264838391)
          ·
            refine ⟨10062150338887126897257587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6708100225924751264838391 10062150338887126897257587)
            ·
              refine ⟨15093225508330690345886381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10062150338887126897257587 15093225508330690345886381)
              ·
                refine ⟨5659959565624008879707393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15093225508330690345886381 5659959565624008879707393)
                ·
                  refine ⟨4244969674218006659780545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5659959565624008879707393 4244969674218006659780545)
                  ·
                    refine ⟨3183727255663504994835409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4244969674218006659780545 3183727255663504994835409)
                    ·
                      refine ⟨2387795441747628746126557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3183727255663504994835409 2387795441747628746126557)
                      ·
                        rfl

theorem cell23_4650215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_4650215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4650215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4650215 prefixEnd_4650215 := by exact prefixLift 4650215
  have htrace : WordTrace (prefixWord ++ tailWord_4650215) baseStart_4650215 baseEnd_4650215 := by
    simpa [prefixWord, tailWord_4650215, baseEnd_4650215] using wordTrace_append hprefix tailTrace_4650215
  have hstable : (prefixWord ++ tailWord_4650215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4650215).length < 2 ^ (prefixWord ++ tailWord_4650215).sum := by decide
  have hdescent : baseEnd_4650215 < baseStart_4650215 := by decide
  rcases family_descends (prefixWord ++ tailWord_4650215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4650234 : List Nat := [3, 1, 1, 1, 1, 4, 4, 1, 2, 5]
def baseStart_4650234 : Nat := 118140960795 + 4650234 * 2 ^ 59
def prefixEnd_4650234 : Nat := 4983230072969 + 3 ^ 40 * 4650234 * 2
def baseEnd_4650234 : Nat := 795935065960021390596323

theorem tailTrace_4650234 : CollatzResearch.WordTrace tailWord_4650234 prefixEnd_4650234 795935065960021390596323 := by
  unfold tailWord_4650234
  simp only [CollatzResearch.WordTrace]
  refine ⟨42401991958750972395769439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113071978556669259722051837 42401991958750972395769439)
  ·
    refine ⟨63602987938126458593654159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42401991958750972395769439 63602987938126458593654159)
    ·
      refine ⟨95404481907189687890481239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63602987938126458593654159 95404481907189687890481239)
      ·
        refine ⟨143106722860784531835721859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95404481907189687890481239 143106722860784531835721859)
        ·
          refine ⟨214660084291176797753582789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143106722860784531835721859 214660084291176797753582789)
          ·
            refine ⟨40248765804595649578796773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 214660084291176797753582789 40248765804595649578796773)
            ·
              refine ⟨7546643588361684296024395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40248765804595649578796773 7546643588361684296024395)
              ·
                refine ⟨11319965382542526444036593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7546643588361684296024395 11319965382542526444036593)
                ·
                  refine ⟨8489974036906894833027445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11319965382542526444036593 8489974036906894833027445)
                  ·
                    refine ⟨795935065960021390596323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8489974036906894833027445 795935065960021390596323)
                    ·
                      rfl

theorem cell23_4650234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 1, 2, 5].length) (baseStart_4650234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4650234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4650234 prefixEnd_4650234 := by exact prefixLift 4650234
  have htrace : WordTrace (prefixWord ++ tailWord_4650234) baseStart_4650234 baseEnd_4650234 := by
    simpa [prefixWord, tailWord_4650234, baseEnd_4650234] using wordTrace_append hprefix tailTrace_4650234
  have hstable : (prefixWord ++ tailWord_4650234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4650234).length < 2 ^ (prefixWord ++ tailWord_4650234).sum := by decide
  have hdescent : baseEnd_4650234 < baseStart_4650234 := by decide
  rcases family_descends (prefixWord ++ tailWord_4650234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4650244 : List Nat := [2, 3, 2, 2, 2, 1, 1, 2, 1, 2, 5]
def baseStart_4650244 : Nat := 118140960795 + 4650244 * 2 ^ 59
def prefixEnd_4650244 : Nat := 4983230072969 + 3 ^ 40 * 4650244 * 2
def baseEnd_4650244 : Nat := 2387810332686609132663923

theorem tailTrace_4650244 : CollatzResearch.WordTrace tailWord_4650244 prefixEnd_4650244 2387810332686609132663923 := by
  unfold tailWord_4650244
  simp only [CollatzResearch.WordTrace]
  refine ⟨84804166282483830645470893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113072221709978440860627857 84804166282483830645470893)
  ·
    refine ⟨31801562355931436492051585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84804166282483830645470893 31801562355931436492051585)
    ·
      refine ⟨23851171766948577369038689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31801562355931436492051585 23851171766948577369038689)
      ·
        refine ⟨17888378825211433026779017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23851171766948577369038689 17888378825211433026779017)
        ·
          refine ⟨13416284118908574770084263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17888378825211433026779017 13416284118908574770084263)
          ·
            refine ⟨20124426178362862155126395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13416284118908574770084263 20124426178362862155126395)
            ·
              refine ⟨30186639267544293232689593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20124426178362862155126395 30186639267544293232689593)
              ·
                refine ⟨22639979450658219924517195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30186639267544293232689593 22639979450658219924517195)
                ·
                  refine ⟨33959969175987329886775793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22639979450658219924517195 33959969175987329886775793)
                  ·
                    refine ⟨25469976881990497415081845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33959969175987329886775793 25469976881990497415081845)
                    ·
                      refine ⟨2387810332686609132663923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25469976881990497415081845 2387810332686609132663923)
                      ·
                        rfl

theorem cell23_4650244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_4650244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4650244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4650244 prefixEnd_4650244 := by exact prefixLift 4650244
  have htrace : WordTrace (prefixWord ++ tailWord_4650244) baseStart_4650244 baseEnd_4650244 := by
    simpa [prefixWord, tailWord_4650244, baseEnd_4650244] using wordTrace_append hprefix tailTrace_4650244
  have hstable : (prefixWord ++ tailWord_4650244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4650244).length < 2 ^ (prefixWord ++ tailWord_4650244).sum := by decide
  have hdescent : baseEnd_4650244 < baseStart_4650244 := by decide
  rcases family_descends (prefixWord ++ tailWord_4650244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4650257 : List Nat := [1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 5]
def baseStart_4650257 : Nat := 118140960795 + 4650257 * 2 ^ 59
def prefixEnd_4650257 : Nat := 4983230072969 + 3 ^ 40 * 4650257 * 2
def baseEnd_4650257 : Nat := 2387817007935117581801363

theorem tailTrace_4650257 : CollatzResearch.WordTrace tailWord_4650257 prefixEnd_4650257 2387817007935117581801363 := by
  unfold tailWord_4650257
  simp only [CollatzResearch.WordTrace]
  refine ⟨169608806713920564511165025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113072537809280376340776683 169608806713920564511165025)
  ·
    refine ⟨127206605035440423383373769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169608806713920564511165025 127206605035440423383373769)
    ·
      refine ⟨95404953776580317537530327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127206605035440423383373769 95404953776580317537530327)
      ·
        refine ⟨143107430664870476306295491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95404953776580317537530327 143107430664870476306295491)
        ·
          refine ⟨214661145997305714459443237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143107430664870476306295491 214661145997305714459443237)
          ·
            refine ⟨40248964874494821461145607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 214661145997305714459443237 40248964874494821461145607)
            ·
              refine ⟨60373447311742232191718411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40248964874494821461145607 60373447311742232191718411)
              ·
                refine ⟨90560170967613348287577617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60373447311742232191718411 90560170967613348287577617)
                ·
                  refine ⟨67920128225710011215683213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90560170967613348287577617 67920128225710011215683213)
                  ·
                    refine ⟨25470048084641254205881205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 67920128225710011215683213 25470048084641254205881205)
                    ·
                      refine ⟨2387817007935117581801363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25470048084641254205881205 2387817007935117581801363)
                      ·
                        rfl

theorem cell23_4650257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 5].length) (baseStart_4650257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4650257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4650257 prefixEnd_4650257 := by exact prefixLift 4650257
  have htrace : WordTrace (prefixWord ++ tailWord_4650257) baseStart_4650257 baseEnd_4650257 := by
    simpa [prefixWord, tailWord_4650257, baseEnd_4650257] using wordTrace_append hprefix tailTrace_4650257
  have hstable : (prefixWord ++ tailWord_4650257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4650257).length < 2 ^ (prefixWord ++ tailWord_4650257).sum := by decide
  have hdescent : baseEnd_4650257 < baseStart_4650257 := by decide
  rcases family_descends (prefixWord ++ tailWord_4650257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4650267 : List Nat := [1, 1, 1, 1, 1, 1, 5, 2, 2, 4, 4]
def baseStart_4650267 : Nat := 118140960795 + 4650267 * 2 ^ 59
def prefixEnd_4650267 : Nat := 4983230072969 + 3 ^ 40 * 4650267 * 2
def baseEnd_4650267 : Nat := 2387822142741662542676317

theorem tailTrace_4650267 : CollatzResearch.WordTrace tailWord_4650267 prefixEnd_4650267 2387822142741662542676317 := by
  unfold tailWord_4650267
  simp only [CollatzResearch.WordTrace]
  refine ⟨169609171443884336219029055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113072780962589557479352703 169609171443884336219029055)
  ·
    refine ⟨254413757165826504328543583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169609171443884336219029055 254413757165826504328543583)
    ·
      refine ⟨381620635748739756492815375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254413757165826504328543583 381620635748739756492815375)
      ·
        refine ⟨572430953623109634739223063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 381620635748739756492815375 572430953623109634739223063)
        ·
          refine ⟨858646430434664452108834595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 572430953623109634739223063 858646430434664452108834595)
          ·
            refine ⟨1287969645651996678163251893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 858646430434664452108834595 1287969645651996678163251893)
            ·
              refine ⟨120747154279874688577804865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1287969645651996678163251893 120747154279874688577804865)
              ·
                refine ⟨90560365709906016433353649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 120747154279874688577804865 90560365709906016433353649)
                ·
                  refine ⟨67920274282429512325015237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90560365709906016433353649 67920274282429512325015237)
                  ·
                    refine ⟨12735051427955533560940357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 67920274282429512325015237 12735051427955533560940357)
                    ·
                      refine ⟨2387822142741662542676317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12735051427955533560940357 2387822142741662542676317)
                      ·
                        rfl

theorem cell23_4650267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 4, 4].length) (baseStart_4650267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4650267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4650267 prefixEnd_4650267 := by exact prefixLift 4650267
  have htrace : WordTrace (prefixWord ++ tailWord_4650267) baseStart_4650267 baseEnd_4650267 := by
    simpa [prefixWord, tailWord_4650267, baseEnd_4650267] using wordTrace_append hprefix tailTrace_4650267
  have hstable : (prefixWord ++ tailWord_4650267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4650267).length < 2 ^ (prefixWord ++ tailWord_4650267).sum := by decide
  have hdescent : baseEnd_4650267 < baseStart_4650267 := by decide
  rcases family_descends (prefixWord ++ tailWord_4650267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4650291 : List Nat := [1, 1, 1, 2, 5, 2, 3, 1, 2, 2, 3]
def baseStart_4650291 : Nat := 118140960795 + 4650291 * 2 ^ 59
def prefixEnd_4650291 : Nat := 4983230072969 + 3 ^ 40 * 4650291 * 2
def baseEnd_4650291 : Nat := 2387834466277370448776207

theorem tailTrace_4650291 : CollatzResearch.WordTrace tailWord_4650291 prefixEnd_4650291 2387834466277370448776207 := by
  unfold tailWord_4650291
  simp only [CollatzResearch.WordTrace]
  refine ⟨169610046795797388317902727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113073364530531592211935151 169610046795797388317902727)
  ·
    refine ⟨254415070193696082476854091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169610046795797388317902727 254415070193696082476854091)
    ·
      refine ⟨381622605290544123715281137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254415070193696082476854091 381622605290544123715281137)
      ·
        refine ⟨286216953967908092786460853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 381622605290544123715281137 286216953967908092786460853)
        ·
          refine ⟨26832839434491383698730705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 286216953967908092786460853 26832839434491383698730705)
          ·
            refine ⟨20124629575868537774048029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26832839434491383698730705 20124629575868537774048029)
            ·
              refine ⟨7546736090950701665268011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20124629575868537774048029 7546736090950701665268011)
              ·
                refine ⟨11320104136426052497902017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7546736090950701665268011 11320104136426052497902017)
                ·
                  refine ⟨8490078102319539373426513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11320104136426052497902017 8490078102319539373426513)
                  ·
                    refine ⟨6367558576739654530069885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8490078102319539373426513 6367558576739654530069885)
                    ·
                      refine ⟨2387834466277370448776207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6367558576739654530069885 2387834466277370448776207)
                      ·
                        rfl

theorem cell23_4650291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 1, 2, 2, 3].length) (baseStart_4650291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4650291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4650291 prefixEnd_4650291 := by exact prefixLift 4650291
  have htrace : WordTrace (prefixWord ++ tailWord_4650291) baseStart_4650291 baseEnd_4650291 := by
    simpa [prefixWord, tailWord_4650291, baseEnd_4650291] using wordTrace_append hprefix tailTrace_4650291
  have hstable : (prefixWord ++ tailWord_4650291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4650291).length < 2 ^ (prefixWord ++ tailWord_4650291).sum := by decide
  have hdescent : baseEnd_4650291 < baseStart_4650291 := by decide
  rcases family_descends (prefixWord ++ tailWord_4650291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4650298 : List Nat := [3, 1, 1, 1, 4, 1, 4, 3, 1, 4]
def baseStart_4650298 : Nat := 118140960795 + 4650298 * 2 ^ 59
def prefixEnd_4650298 : Nat := 4983230072969 + 3 ^ 40 * 4650298 * 2
def baseEnd_4650298 : Nat := 795946020213983973796225

theorem tailTrace_4650298 : CollatzResearch.WordTrace tailWord_4650298 prefixEnd_4650298 795946020213983973796225 := by
  unfold tailWord_4650298
  simp only [CollatzResearch.WordTrace]
  refine ⟨42402575526693007128351887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113073534737848019008938365 42402575526693007128351887)
  ·
    refine ⟨63603863290039510692527831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42402575526693007128351887 63603863290039510692527831)
    ·
      refine ⟨95405794935059266038791747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63603863290039510692527831 95405794935059266038791747)
      ·
        refine ⟨143108692402588899058187621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95405794935059266038791747 143108692402588899058187621)
        ·
          refine ⟨26832879825485418573410179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 143108692402588899058187621 26832879825485418573410179)
          ·
            refine ⟨40249319738228127860115269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26832879825485418573410179 40249319738228127860115269)
            ·
              refine ⟨7546747450917773973771613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40249319738228127860115269 7546747450917773973771613)
              ·
                refine ⟨2830030294094165240164355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7546747450917773973771613 2830030294094165240164355)
                ·
                  refine ⟨4245045441141247860246533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2830030294094165240164355 4245045441141247860246533)
                  ·
                    refine ⟨795946020213983973796225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4245045441141247860246533 795946020213983973796225)
                    ·
                      rfl

theorem cell23_4650298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 3, 1, 4].length) (baseStart_4650298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4650298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4650298 prefixEnd_4650298 := by exact prefixLift 4650298
  have htrace : WordTrace (prefixWord ++ tailWord_4650298) baseStart_4650298 baseEnd_4650298 := by
    simpa [prefixWord, tailWord_4650298, baseEnd_4650298] using wordTrace_append hprefix tailTrace_4650298
  have hstable : (prefixWord ++ tailWord_4650298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4650298).length < 2 ^ (prefixWord ++ tailWord_4650298).sum := by decide
  have hdescent : baseEnd_4650298 < baseStart_4650298 := by decide
  rcases family_descends (prefixWord ++ tailWord_4650298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4650311 : List Nat := [1, 1, 4, 1, 2, 5, 1, 2, 6]
def baseStart_4650311 : Nat := 118140960795 + 4650311 * 2 ^ 59
def prefixEnd_4650311 : Nat := 4983230072969 + 3 ^ 40 * 4650311 * 2
def baseEnd_4650311 : Nat := 265316081765606707836235

theorem tailTrace_4650311 : CollatzResearch.WordTrace tailWord_4650311 prefixEnd_4650311 265316081765606707836235 := by
  unfold tailWord_4650311
  simp only [CollatzResearch.WordTrace]
  refine ⟨169610776255724931733630787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113073850837149954489087191 169610776255724931733630787)
  ·
    refine ⟨254416164383587397600446181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169610776255724931733630787 254416164383587397600446181)
    ·
      refine ⟨47703030821922637050083659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 254416164383587397600446181 47703030821922637050083659)
      ·
        refine ⟨71554546232883955575125489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47703030821922637050083659 71554546232883955575125489)
        ·
          refine ⟨53665909674662966681344117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71554546232883955575125489 53665909674662966681344117)
          ·
            refine ⟨5031179031999653126376011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53665909674662966681344117 5031179031999653126376011)
            ·
              refine ⟨7546768547999479689564017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5031179031999653126376011 7546768547999479689564017)
              ·
                refine ⟨5660076410999609767173013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7546768547999479689564017 5660076410999609767173013)
                ·
                  refine ⟨265316081765606707836235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5660076410999609767173013 265316081765606707836235)
                  ·
                    rfl

theorem cell23_4650311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 2, 6].length) (baseStart_4650311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4650311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4650311 prefixEnd_4650311 := by exact prefixLift 4650311
  have htrace : WordTrace (prefixWord ++ tailWord_4650311) baseStart_4650311 baseEnd_4650311 := by
    simpa [prefixWord, tailWord_4650311, baseEnd_4650311] using wordTrace_append hprefix tailTrace_4650311
  have hstable : (prefixWord ++ tailWord_4650311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4650311).length < 2 ^ (prefixWord ++ tailWord_4650311).sum := by decide
  have hdescent : baseEnd_4650311 < baseStart_4650311 := by decide
  rcases family_descends (prefixWord ++ tailWord_4650311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4650338 : List Nat := [3, 3, 2, 1, 1, 1, 1, 4, 3, 1, 3]
def baseStart_4650338 : Nat := 118140960795 + 4650338 * 2 ^ 59
def prefixEnd_4650338 : Nat := 4983230072969 + 3 ^ 40 * 4650338 * 2
def baseEnd_4650338 : Nat := 2387858599868131764888491

theorem tailTrace_4650338 : CollatzResearch.WordTrace tailWord_4650338 prefixEnd_4650338 2387858599868131764888491 := by
  unfold tailWord_4650338
  simp only [CollatzResearch.WordTrace]
  refine ⟨42402940256656778836215917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113074507351084743563242445 42402940256656778836215917)
  ·
    refine ⟨15901102596246292063580969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42402940256656778836215917 15901102596246292063580969)
    ·
      refine ⟨11925826947184719047685727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15901102596246292063580969 11925826947184719047685727)
      ·
        refine ⟨17888740420777078571528591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11925826947184719047685727 17888740420777078571528591)
        ·
          refine ⟨26833110631165617857292887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17888740420777078571528591 26833110631165617857292887)
          ·
            refine ⟨40249665946748426785939331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26833110631165617857292887 40249665946748426785939331)
            ·
              refine ⟨60374498920122640178908997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40249665946748426785939331 60374498920122640178908997)
              ·
                refine ⟨11320218547522995033545437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60374498920122640178908997 11320218547522995033545437)
                ·
                  refine ⟨4245081955321123137579539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11320218547522995033545437 4245081955321123137579539)
                  ·
                    refine ⟨6367622932981684706369309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4245081955321123137579539 6367622932981684706369309)
                    ·
                      refine ⟨2387858599868131764888491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6367622932981684706369309 2387858599868131764888491)
                      ·
                        rfl

theorem cell23_4650338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_4650338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4650338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4650338 prefixEnd_4650338 := by exact prefixLift 4650338
  have htrace : WordTrace (prefixWord ++ tailWord_4650338) baseStart_4650338 baseEnd_4650338 := by
    simpa [prefixWord, tailWord_4650338, baseEnd_4650338] using wordTrace_append hprefix tailTrace_4650338
  have hstable : (prefixWord ++ tailWord_4650338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4650338).length < 2 ^ (prefixWord ++ tailWord_4650338).sum := by decide
  have hdescent : baseEnd_4650338 < baseStart_4650338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4650338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4650341 : List Nat := [1, 3, 1, 3, 1, 2, 4, 2, 1, 5]
def baseStart_4650341 : Nat := 118140960795 + 4650341 * 2 ^ 59
def prefixEnd_4650341 : Nat := 4983230072969 + 3 ^ 40 * 4650341 * 2
def baseEnd_4650341 : Nat := 795953380103365084383659

theorem tailTrace_4650341 : CollatzResearch.WordTrace tailWord_4650341 prefixEnd_4650341 795953380103365084383659 := by
  unfold tailWord_4650341
  simp only [CollatzResearch.WordTrace]
  refine ⟨169611870445616246857222877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113074580297077497904815251 169611870445616246857222877)
  ·
    refine ⟨63604451417106092571458579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169611870445616246857222877 63604451417106092571458579)
    ·
      refine ⟨95406677125659138857187869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63604451417106092571458579 95406677125659138857187869)
      ·
        refine ⟨35777503922122177071445451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95406677125659138857187869 35777503922122177071445451)
        ·
          refine ⟨53666255883183265607168177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35777503922122177071445451 53666255883183265607168177)
          ·
            refine ⟨40249691912387449205376133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53666255883183265607168177 40249691912387449205376133)
            ·
              refine ⟨7546817233572646726008025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40249691912387449205376133 7546817233572646726008025)
              ·
                refine ⟨5660112925179485044506019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7546817233572646726008025 5660112925179485044506019)
                ·
                  refine ⟨8490169387769227566759029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5660112925179485044506019 8490169387769227566759029)
                  ·
                    refine ⟨795953380103365084383659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8490169387769227566759029 795953380103365084383659)
                    ·
                      rfl

theorem cell23_4650341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 2, 1, 5].length) (baseStart_4650341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4650341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4650341 prefixEnd_4650341 := by exact prefixLift 4650341
  have htrace : WordTrace (prefixWord ++ tailWord_4650341) baseStart_4650341 baseEnd_4650341 := by
    simpa [prefixWord, tailWord_4650341, baseEnd_4650341] using wordTrace_append hprefix tailTrace_4650341
  have hstable : (prefixWord ++ tailWord_4650341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4650341).length < 2 ^ (prefixWord ++ tailWord_4650341).sum := by decide
  have hdescent : baseEnd_4650341 < baseStart_4650341 := by decide
  rcases family_descends (prefixWord ++ tailWord_4650341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4650354 : List Nat := [3, 2, 1, 2, 1, 2, 2, 1, 3, 6]
def baseStart_4650354 : Nat := 118140960795 + 4650354 * 2 ^ 59
def prefixEnd_4650354 : Nat := 4983230072969 + 3 ^ 40 * 4650354 * 2
def baseEnd_4650354 : Nat := 795955605186201234096139

theorem tailTrace_4650354 : CollatzResearch.WordTrace tailWord_4650354 prefixEnd_4650354 795955605186201234096139 := by
  unfold tailWord_4650354
  simp only [CollatzResearch.WordTrace]
  refine ⟨42403086148642287519361529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113074896396379433384964077 42403086148642287519361529)
  ·
    refine ⟨31802314611481715639521147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42403086148642287519361529 31802314611481715639521147)
    ·
      refine ⟨47703471917222573459281721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31802314611481715639521147 47703471917222573459281721)
      ·
        refine ⟨35777603937916930094461291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47703471917222573459281721 35777603937916930094461291)
        ·
          refine ⟨53666405906875395141691937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35777603937916930094461291 53666405906875395141691937)
          ·
            refine ⟨40249804430156546356268953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53666405906875395141691937 40249804430156546356268953)
            ·
              refine ⟨30187353322617409767201715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40249804430156546356268953 30187353322617409767201715)
              ·
                refine ⟨45281029983926114650802573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30187353322617409767201715 45281029983926114650802573)
                ·
                  refine ⟨16980386243972292994050965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45281029983926114650802573 16980386243972292994050965)
                  ·
                    refine ⟨795955605186201234096139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16980386243972292994050965 795955605186201234096139)
                    ·
                      rfl

theorem cell23_4650354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 3, 6].length) (baseStart_4650354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4650354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4650354 prefixEnd_4650354 := by exact prefixLift 4650354
  have htrace : WordTrace (prefixWord ++ tailWord_4650354) baseStart_4650354 baseEnd_4650354 := by
    simpa [prefixWord, tailWord_4650354, baseEnd_4650354] using wordTrace_append hprefix tailTrace_4650354
  have hstable : (prefixWord ++ tailWord_4650354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4650354).length < 2 ^ (prefixWord ++ tailWord_4650354).sum := by decide
  have hdescent : baseEnd_4650354 < baseStart_4650354 := by decide
  rcases family_descends (prefixWord ++ tailWord_4650354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4650361 : List Nat := [1, 2, 1, 3, 2, 1, 4, 3, 1, 1, 4]
def baseStart_4650361 : Nat := 118140960795 + 4650361 * 2 ^ 59
def prefixEnd_4650361 : Nat := 4983230072969 + 3 ^ 40 * 4650361 * 2
def baseEnd_4650361 : Nat := 2387870409923185174900885

theorem tailTrace_4650361 : CollatzResearch.WordTrace tailWord_4650361 prefixEnd_4650361 2387870409923185174900885 := by
  unfold tailWord_4650361
  simp only [CollatzResearch.WordTrace]
  refine ⟨169612599905543790272950937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113075066603695860181967291 169612599905543790272950937)
  ·
    refine ⟨127209449929157842704713203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169612599905543790272950937 127209449929157842704713203)
    ·
      refine ⟨190814174893736764057069805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127209449929157842704713203 190814174893736764057069805)
      ·
        refine ⟨71555315585151286521401177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 190814174893736764057069805 71555315585151286521401177)
        ·
          refine ⟨53666486688863464891050883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71555315585151286521401177 53666486688863464891050883)
          ·
            refine ⟨80499730033295197336576325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53666486688863464891050883 80499730033295197336576325)
            ·
              refine ⟨15093699381242849500608061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 80499730033295197336576325 15093699381242849500608061)
              ·
                refine ⟨5660137267966068562728023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15093699381242849500608061 5660137267966068562728023)
                ·
                  refine ⟨8490205901949102844092035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5660137267966068562728023 8490205901949102844092035)
                  ·
                    refine ⟨12735308852923654266138053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8490205901949102844092035 12735308852923654266138053)
                    ·
                      refine ⟨2387870409923185174900885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12735308852923654266138053 2387870409923185174900885)
                      ·
                        rfl

theorem cell23_4650361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 3, 1, 1, 4].length) (baseStart_4650361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4650361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4650361 prefixEnd_4650361 := by exact prefixLift 4650361
  have htrace : WordTrace (prefixWord ++ tailWord_4650361) baseStart_4650361 baseEnd_4650361 := by
    simpa [prefixWord, tailWord_4650361, baseEnd_4650361] using wordTrace_append hprefix tailTrace_4650361
  have hstable : (prefixWord ++ tailWord_4650361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4650361).length < 2 ^ (prefixWord ++ tailWord_4650361).sum := by decide
  have hdescent : baseEnd_4650361 < baseStart_4650361 := by decide
  rcases family_descends (prefixWord ++ tailWord_4650361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4650371 : List Nat := [1, 1, 1, 3, 5, 1, 2, 1, 4, 4]
def baseStart_4650371 : Nat := 118140960795 + 4650371 * 2 ^ 59
def prefixEnd_4650371 : Nat := 4983230072969 + 3 ^ 40 * 4650371 * 2
def baseEnd_4650371 : Nat := 795958514909910045258613

theorem tailTrace_4650371 : CollatzResearch.WordTrace tailWord_4650371 prefixEnd_4650371 795958514909910045258613 := by
  unfold tailWord_4650371
  simp only [CollatzResearch.WordTrace]
  refine ⟨169612964635507561980814967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113075309757005041320543311 169612964635507561980814967)
  ·
    refine ⟨254419446953261342971222451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169612964635507561980814967 254419446953261342971222451)
    ·
      refine ⟨381629170429892014456833677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254419446953261342971222451 381629170429892014456833677)
      ·
        refine ⟨143110938911209505421312629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 381629170429892014456833677 143110938911209505421312629)
        ·
          refine ⟨13416650522925891133248059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 143110938911209505421312629 13416650522925891133248059)
          ·
            refine ⟨20124975784388836699872089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13416650522925891133248059 20124975784388836699872089)
            ·
              refine ⟨15093731838291627524904067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20124975784388836699872089 15093731838291627524904067)
              ·
                refine ⟨22640597757437441287356101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15093731838291627524904067 22640597757437441287356101)
                ·
                  refine ⟨4245112079519520241379269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22640597757437441287356101 4245112079519520241379269)
                  ·
                    refine ⟨795958514909910045258613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4245112079519520241379269 795958514909910045258613)
                    ·
                      rfl

theorem cell23_4650371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 4, 4].length) (baseStart_4650371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4650371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4650371 prefixEnd_4650371 := by exact prefixLift 4650371
  have htrace : WordTrace (prefixWord ++ tailWord_4650371) baseStart_4650371 baseEnd_4650371 := by
    simpa [prefixWord, tailWord_4650371, baseEnd_4650371] using wordTrace_append hprefix tailTrace_4650371
  have hstable : (prefixWord ++ tailWord_4650371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4650371).length < 2 ^ (prefixWord ++ tailWord_4650371).sum := by decide
  have hdescent : baseEnd_4650371 < baseStart_4650371 := by decide
  rcases family_descends (prefixWord ++ tailWord_4650371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4650372 : List Nat := [2, 3, 2, 1, 1, 4, 3, 2, 1, 1, 3]
def baseStart_4650372 : Nat := 118140960795 + 4650372 * 2 ^ 59
def prefixEnd_4650372 : Nat := 4983230072969 + 3 ^ 40 * 4650372 * 2
def baseEnd_4650372 : Nat := 2387876058210384631863335

theorem tailTrace_4650372 : CollatzResearch.WordTrace tailWord_4650372 prefixEnd_4650372 2387876058210384631863335 := by
  unfold tailWord_4650372
  simp only [CollatzResearch.WordTrace]
  refine ⟨84806500554251969575800685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113075334072335959434400913 84806500554251969575800685)
  ·
    refine ⟨31802437707844488590925257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84806500554251969575800685 31802437707844488590925257)
    ·
      refine ⟨23851828280883366443193943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31802437707844488590925257 23851828280883366443193943)
      ·
        refine ⟨35777742421325049664790915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23851828280883366443193943 35777742421325049664790915)
        ·
          refine ⟨53666613631987574497186373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35777742421325049664790915 53666613631987574497186373)
          ·
            refine ⟨10062490055997670218222445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53666613631987574497186373 10062490055997670218222445)
            ·
              refine ⟨3773433770999126331833417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10062490055997670218222445 3773433770999126331833417)
              ·
                refine ⟨2830075328249344748875063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3773433770999126331833417 2830075328249344748875063)
                ·
                  refine ⟨4245112992374017123312595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2830075328249344748875063 4245112992374017123312595)
                  ·
                    refine ⟨6367669488561025684968893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4245112992374017123312595 6367669488561025684968893)
                    ·
                      refine ⟨2387876058210384631863335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6367669488561025684968893 2387876058210384631863335)
                      ·
                        rfl

theorem cell23_4650372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 3, 2, 1, 1, 3].length) (baseStart_4650372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4650372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4650372 prefixEnd_4650372 := by exact prefixLift 4650372
  have htrace : WordTrace (prefixWord ++ tailWord_4650372) baseStart_4650372 baseEnd_4650372 := by
    simpa [prefixWord, tailWord_4650372, baseEnd_4650372] using wordTrace_append hprefix tailTrace_4650372
  have hstable : (prefixWord ++ tailWord_4650372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4650372).length < 2 ^ (prefixWord ++ tailWord_4650372).sum := by decide
  have hdescent : baseEnd_4650372 < baseStart_4650372 := by decide
  rcases family_descends (prefixWord ++ tailWord_4650372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4650424 : List Nat := [2, 1, 2, 1, 2, 2, 2, 2, 2, 2, 5]
def baseStart_4650424 : Nat := 118140960795 + 4650424 * 2 ^ 59
def prefixEnd_4650424 : Nat := 4983230072969 + 3 ^ 40 * 4650424 * 2
def baseEnd_4650424 : Nat := 2387902759204418428413095

theorem tailTrace_4650424 : CollatzResearch.WordTrace tailWord_4650424 prefixEnd_4650424 2387902759204418428413095 := by
  unfold tailWord_4650424
  simp only [CollatzResearch.WordTrace]
  refine ⟨84807448852157776016247163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113076598469543701354996217 84807448852157776016247163)
  ·
    refine ⟨127211173278236664024370745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84807448852157776016247163 127211173278236664024370745)
    ·
      refine ⟨95408379958677498018278059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127211173278236664024370745 95408379958677498018278059)
      ·
        refine ⟨143112569938016247027417089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95408379958677498018278059 143112569938016247027417089)
        ·
          refine ⟨107334427453512185270562817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143112569938016247027417089 107334427453512185270562817)
          ·
            refine ⟨80500820590134138952922113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107334427453512185270562817 80500820590134138952922113)
            ·
              refine ⟨60375615442600604214691585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80500820590134138952922113 60375615442600604214691585)
              ·
                refine ⟨45281711581950453161018689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60375615442600604214691585 45281711581950453161018689)
                ·
                  refine ⟨33961283686462839870764017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45281711581950453161018689 33961283686462839870764017)
                  ·
                    refine ⟨25470962764847129903073013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33961283686462839870764017 25470962764847129903073013)
                    ·
                      refine ⟨2387902759204418428413095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25470962764847129903073013 2387902759204418428413095)
                      ·
                        rfl

theorem cell23_4650424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 2, 2, 5].length) (baseStart_4650424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4650424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4650424 prefixEnd_4650424 := by exact prefixLift 4650424
  have htrace : WordTrace (prefixWord ++ tailWord_4650424) baseStart_4650424 baseEnd_4650424 := by
    simpa [prefixWord, tailWord_4650424, baseEnd_4650424] using wordTrace_append hprefix tailTrace_4650424
  have hstable : (prefixWord ++ tailWord_4650424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4650424).length < 2 ^ (prefixWord ++ tailWord_4650424).sum := by decide
  have hdescent : baseEnd_4650424 < baseStart_4650424 := by decide
  rcases family_descends (prefixWord ++ tailWord_4650424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4650481 : List Nat := [1, 2, 2, 2, 3, 2, 1, 2, 2, 2, 4]
def baseStart_4650481 : Nat := 118140960795 + 4650481 * 2 ^ 59
def prefixEnd_4650481 : Nat := 4983230072969 + 3 ^ 40 * 4650481 * 2
def baseEnd_4650481 : Nat := 2387932027601724705400333

theorem tailTrace_4650481 : CollatzResearch.WordTrace tailWord_4650481 prefixEnd_4650481 2387932027601724705400333 := by
  unfold tailWord_4650481
  simp only [CollatzResearch.WordTrace]
  refine ⟨169616976665109050767319297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113077984443406033844879531 169616976665109050767319297)
  ·
    refine ⟨127212732498831788075489473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169616976665109050767319297 127212732498831788075489473)
    ·
      refine ⟨95409549374123841056617105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127212732498831788075489473 95409549374123841056617105)
      ·
        refine ⟨71557162030592880792462829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95409549374123841056617105 71557162030592880792462829)
        ·
          refine ⟨26833935761472330297173561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71557162030592880792462829 26833935761472330297173561)
          ·
            refine ⟨20125451821104247722880171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26833935761472330297173561 20125451821104247722880171)
            ·
              refine ⟨30188177731656371584320257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20125451821104247722880171 30188177731656371584320257)
              ·
                refine ⟨22641133298742278688240193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30188177731656371584320257 22641133298742278688240193)
                ·
                  refine ⟨16980849974056709016180145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22641133298742278688240193 16980849974056709016180145)
                  ·
                    refine ⟨12735637480542531762135109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16980849974056709016180145 12735637480542531762135109)
                    ·
                      refine ⟨2387932027601724705400333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12735637480542531762135109 2387932027601724705400333)
                      ·
                        rfl

theorem cell23_4650481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 2, 2, 4].length) (baseStart_4650481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4650481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4650481 prefixEnd_4650481 := by exact prefixLift 4650481
  have htrace : WordTrace (prefixWord ++ tailWord_4650481) baseStart_4650481 baseEnd_4650481 := by
    simpa [prefixWord, tailWord_4650481, baseEnd_4650481] using wordTrace_append hprefix tailTrace_4650481
  have hstable : (prefixWord ++ tailWord_4650481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4650481).length < 2 ^ (prefixWord ++ tailWord_4650481).sum := by decide
  have hdescent : baseEnd_4650481 < baseStart_4650481 := by decide
  rcases family_descends (prefixWord ++ tailWord_4650481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4650538 : List Nat := [3, 1, 4, 1, 1, 1, 3, 2, 2, 5]
def baseStart_4650538 : Nat := 118140960795 + 4650538 * 2 ^ 59
def prefixEnd_4650538 : Nat := 4983230072969 + 3 ^ 40 * 4650538 * 2
def baseEnd_4650538 : Nat := 795987098666343660795857

theorem tailTrace_4650538 : CollatzResearch.WordTrace tailWord_4650538 prefixEnd_4650538 795987098666343660795857 := by
  unfold tailWord_4650538
  simp only [CollatzResearch.WordTrace]
  refine ⟨42404763906475637375536067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113079370417268366334762845 42404763906475637375536067)
  ·
    refine ⟨63607145859713456063304101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42404763906475637375536067 63607145859713456063304101)
    ·
      refine ⟨11926339848696273011869519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63607145859713456063304101 11926339848696273011869519)
      ·
        refine ⟨17889509773044409517804279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11926339848696273011869519 17889509773044409517804279)
        ·
          refine ⟨26834264659566614276706419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17889509773044409517804279 26834264659566614276706419)
          ·
            refine ⟨40251396989349921415059629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26834264659566614276706419 40251396989349921415059629)
            ·
              refine ⟨15094273871006220530647361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40251396989349921415059629 15094273871006220530647361)
              ·
                refine ⟨11320705403254665397985521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15094273871006220530647361 11320705403254665397985521)
                ·
                  refine ⟨8490529052440999048489141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11320705403254665397985521 8490529052440999048489141)
                  ·
                    refine ⟨795987098666343660795857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8490529052440999048489141 795987098666343660795857)
                    ·
                      rfl

theorem cell23_4650538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_4650538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4650538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4650538 prefixEnd_4650538 := by exact prefixLift 4650538
  have htrace : WordTrace (prefixWord ++ tailWord_4650538) baseStart_4650538 baseEnd_4650538 := by
    simpa [prefixWord, tailWord_4650538, baseEnd_4650538] using wordTrace_append hprefix tailTrace_4650538
  have hstable : (prefixWord ++ tailWord_4650538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4650538).length < 2 ^ (prefixWord ++ tailWord_4650538).sum := by decide
  have hdescent : baseEnd_4650538 < baseStart_4650538 := by decide
  rcases family_descends (prefixWord ++ tailWord_4650538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4650542 : List Nat := [4, 1, 3, 1, 2, 2, 3, 2, 5]
def baseStart_4650542 : Nat := 118140960795 + 4650542 * 2 ^ 59
def prefixEnd_4650542 : Nat := 4983230072969 + 3 ^ 40 * 4650542 * 2
def baseEnd_4650542 : Nat := 265329261102405440748617

theorem tailTrace_4650542 : CollatzResearch.WordTrace tailWord_4650542 prefixEnd_4650542 265329261102405440748617 := by
  unfold tailWord_4650542
  simp only [CollatzResearch.WordTrace]
  refine ⟨21202400189736007273161235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113079467678592038790193253 21202400189736007273161235)
  ·
    refine ⟨31803600284604010909741853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21202400189736007273161235 31803600284604010909741853)
    ·
      refine ⟨11926350106726504091153195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31803600284604010909741853 11926350106726504091153195)
      ·
        refine ⟨17889525160089756136729793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11926350106726504091153195 17889525160089756136729793)
        ·
          refine ⟨13417143870067317102547345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17889525160089756136729793 13417143870067317102547345)
          ·
            refine ⟨10062857902550487826910509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13417143870067317102547345 10062857902550487826910509)
            ·
              refine ⟨3773571713456432935091441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10062857902550487826910509 3773571713456432935091441)
              ·
                refine ⟨2830178785092324701318581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3773571713456432935091441 2830178785092324701318581)
                ·
                  refine ⟨265329261102405440748617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2830178785092324701318581 265329261102405440748617)
                  ·
                    rfl

theorem cell23_4650542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 3, 2, 5].length) (baseStart_4650542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4650542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4650542 prefixEnd_4650542 := by exact prefixLift 4650542
  have htrace : WordTrace (prefixWord ++ tailWord_4650542) baseStart_4650542 baseEnd_4650542 := by
    simpa [prefixWord, tailWord_4650542, baseEnd_4650542] using wordTrace_append hprefix tailTrace_4650542
  have hstable : (prefixWord ++ tailWord_4650542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4650542).length < 2 ^ (prefixWord ++ tailWord_4650542).sum := by decide
  have hdescent : baseEnd_4650542 < baseStart_4650542 := by decide
  rcases family_descends (prefixWord ++ tailWord_4650542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4650602 : List Nat := [3, 1, 3, 2, 1, 3, 1, 4, 1, 4]
def baseStart_4650602 : Nat := 118140960795 + 4650602 * 2 ^ 59
def prefixEnd_4650602 : Nat := 4983230072969 + 3 ^ 40 * 4650602 * 2
def baseEnd_4650602 : Nat := 795998052920306243995759

theorem tailTrace_4650602 : CollatzResearch.WordTrace tailWord_4650602 prefixEnd_4650602 795998052920306243995759 := by
  unfold tailWord_4650602
  simp only [CollatzResearch.WordTrace]
  refine ⟨42405347474417672108118515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113080926598447125621649373 42405347474417672108118515)
  ·
    refine ⟨63608021211626508162177773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42405347474417672108118515 63608021211626508162177773)
    ·
      refine ⟨23853007954359940560816665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63608021211626508162177773 23853007954359940560816665)
      ·
        refine ⟨17889755965769955420612499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23853007954359940560816665 17889755965769955420612499)
        ·
          refine ⟨26834633948654933130918749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17889755965769955420612499 26834633948654933130918749)
          ·
            refine ⟨10062987730745599924094531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26834633948654933130918749 10062987730745599924094531)
            ·
              refine ⟨15094481596118399886141797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10062987730745599924094531 15094481596118399886141797)
              ·
                refine ⟨2830215299272199978651587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15094481596118399886141797 2830215299272199978651587)
                ·
                  refine ⟨4245322948908299967977381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2830215299272199978651587 4245322948908299967977381)
                  ·
                    refine ⟨795998052920306243995759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4245322948908299967977381 795998052920306243995759)
                    ·
                      rfl

theorem cell23_4650602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 4, 1, 4].length) (baseStart_4650602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4650602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4650602 prefixEnd_4650602 := by exact prefixLift 4650602
  have htrace : WordTrace (prefixWord ++ tailWord_4650602) baseStart_4650602 baseEnd_4650602 := by
    simpa [prefixWord, tailWord_4650602, baseEnd_4650602] using wordTrace_append hprefix tailTrace_4650602
  have hstable : (prefixWord ++ tailWord_4650602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4650602).length < 2 ^ (prefixWord ++ tailWord_4650602).sum := by decide
  have hdescent : baseEnd_4650602 < baseStart_4650602 := by decide
  rcases family_descends (prefixWord ++ tailWord_4650602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4650625 : List Nat := [1, 2, 4, 2, 1, 2, 1, 1, 5, 1, 3]
def baseStart_4650625 : Nat := 118140960795 + 4650625 * 2 ^ 59
def prefixEnd_4650625 : Nat := 4983230072969 + 3 ^ 40 * 4650625 * 2
def baseEnd_4650625 : Nat := 2388005968815972141999671

theorem tailTrace_4650625 : CollatzResearch.WordTrace tailWord_4650625 prefixEnd_4650625 2388005968815972141999671 := by
  unfold tailWord_4650625
  simp only [CollatzResearch.WordTrace]
  refine ⟨169622228776587363360561329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113081485851058242240374219 169622228776587363360561329)
  ·
    refine ⟨127216671582440522520420997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169622228776587363360561329 127216671582440522520420997)
    ·
      refine ⟨23853125921707597972578937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127216671582440522520420997 23853125921707597972578937)
      ·
        refine ⟨17889844441280698479434203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23853125921707597972578937 17889844441280698479434203)
        ·
          refine ⟨26834766661921047719151305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17889844441280698479434203 26834766661921047719151305)
          ·
            refine ⟨20126074996440785789363479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26834766661921047719151305 20126074996440785789363479)
            ·
              refine ⟨30189112494661178684045219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20126074996440785789363479 30189112494661178684045219)
              ·
                refine ⟨45283668741991768026067829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30189112494661178684045219 45283668741991768026067829)
                ·
                  refine ⟨4245343944561728252443859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45283668741991768026067829 4245343944561728252443859)
                  ·
                    refine ⟨6368015916842592378665789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4245343944561728252443859 6368015916842592378665789)
                    ·
                      refine ⟨2388005968815972141999671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6368015916842592378665789 2388005968815972141999671)
                      ·
                        rfl

theorem cell23_4650625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_4650625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4650625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4650625 prefixEnd_4650625 := by exact prefixLift 4650625
  have htrace : WordTrace (prefixWord ++ tailWord_4650625) baseStart_4650625 baseEnd_4650625 := by
    simpa [prefixWord, tailWord_4650625, baseEnd_4650625] using wordTrace_append hprefix tailTrace_4650625
  have hstable : (prefixWord ++ tailWord_4650625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4650625).length < 2 ^ (prefixWord ++ tailWord_4650625).sum := by decide
  have hdescent : baseEnd_4650625 < baseStart_4650625 := by decide
  rcases family_descends (prefixWord ++ tailWord_4650625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4650641 : List Nat := [1, 2, 2, 1, 1, 1, 1, 5, 3, 6]
def baseStart_4650641 : Nat := 118140960795 + 4650641 * 2 ^ 59
def prefixEnd_4650641 : Nat := 4983230072969 + 3 ^ 40 * 4650641 * 2
def baseEnd_4650641 : Nat := 796004728168814693133199

theorem tailTrace_4650641 : CollatzResearch.WordTrace tailWord_4650641 prefixEnd_4650641 796004728168814693133199 := by
  unfold tailWord_4650641
  simp only [CollatzResearch.WordTrace]
  refine ⟨169622812344529398093143777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113081874896352932062095851 169622812344529398093143777)
  ·
    refine ⟨127217109258397048569857833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169622812344529398093143777 127217109258397048569857833)
    ·
      refine ⟨95412831943797786427393375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127217109258397048569857833 95412831943797786427393375)
      ·
        refine ⟨143119247915696679641090063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95412831943797786427393375 143119247915696679641090063)
        ·
          refine ⟨214678871873545019461635095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143119247915696679641090063 214678871873545019461635095)
          ·
            refine ⟨322018307810317529192452643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214678871873545019461635095 322018307810317529192452643)
            ·
              refine ⟨483027461715476293788678965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 322018307810317529192452643 483027461715476293788678965)
              ·
                refine ⟨45283824535825902542688653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 483027461715476293788678965 45283824535825902542688653)
                ·
                  refine ⟨16981434200934713453508245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45283824535825902542688653 16981434200934713453508245)
                  ·
                    refine ⟨796004728168814693133199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16981434200934713453508245 796004728168814693133199)
                    ·
                      rfl

theorem cell23_4650641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 6].length) (baseStart_4650641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4650641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4650641 prefixEnd_4650641 := by exact prefixLift 4650641
  have htrace : WordTrace (prefixWord ++ tailWord_4650641) baseStart_4650641 baseEnd_4650641 := by
    simpa [prefixWord, tailWord_4650641, baseEnd_4650641] using wordTrace_append hprefix tailTrace_4650641
  have hstable : (prefixWord ++ tailWord_4650641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4650641).length < 2 ^ (prefixWord ++ tailWord_4650641).sum := by decide
  have hdescent : baseEnd_4650641 < baseStart_4650641 := by decide
  rcases family_descends (prefixWord ++ tailWord_4650641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4650671 : List Nat := [1, 1, 2, 1, 2, 4, 2, 10]
def baseStart_4650671 : Nat := 118140960795 + 4650671 * 2 ^ 59
def prefixEnd_4650671 : Nat := 4983230072969 + 3 ^ 40 * 4650671 * 2
def baseEnd_4650671 : Nat := 88445540330595517112017

theorem tailTrace_4650671 : CollatzResearch.WordTrace tailWord_4650671 prefixEnd_4650671 88445540330595517112017 := by
  unfold tailWord_4650671
  simp only [CollatzResearch.WordTrace]
  refine ⟨169623906534420713216735867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113082604356280475477823911 169623906534420713216735867)
  ·
    refine ⟨254435859801631069825103801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169623906534420713216735867 254435859801631069825103801)
    ·
      refine ⟨190826894851223302368827851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 254435859801631069825103801 190826894851223302368827851)
      ·
        refine ⟨286240342276834953553241777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190826894851223302368827851 286240342276834953553241777)
        ·
          refine ⟨214680256707626215164931333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 286240342276834953553241777 214680256707626215164931333)
          ·
            refine ⟨40252548132679915343424625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 214680256707626215164931333 40252548132679915343424625)
            ·
              refine ⟨30189411099509936507568469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40252548132679915343424625 30189411099509936507568469)
              ·
                refine ⟨88445540330595517112017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 30189411099509936507568469 88445540330595517112017)
                ·
                  rfl

theorem cell23_4650671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 10].length) (baseStart_4650671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4650671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4650671 prefixEnd_4650671 := by exact prefixLift 4650671
  have htrace : WordTrace (prefixWord ++ tailWord_4650671) baseStart_4650671 baseEnd_4650671 := by
    simpa [prefixWord, tailWord_4650671, baseEnd_4650671] using wordTrace_append hprefix tailTrace_4650671
  have hstable : (prefixWord ++ tailWord_4650671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4650671).length < 2 ^ (prefixWord ++ tailWord_4650671).sum := by decide
  have hdescent : baseEnd_4650671 < baseStart_4650671 := by decide
  rcases family_descends (prefixWord ++ tailWord_4650671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4650682 : List Nat := [3, 1, 1, 1, 2, 4, 2, 2, 3, 2, 2]
def baseStart_4650682 : Nat := 118140960795 + 4650682 * 2 ^ 59
def prefixEnd_4650682 : Nat := 4983230072969 + 3 ^ 40 * 4650682 * 2
def baseEnd_4650682 : Nat := 2388035237213278418986909

theorem tailTrace_4650682 : CollatzResearch.WordTrace tailWord_4650682 prefixEnd_4650682 2388035237213278418986909 := by
  unfold tailWord_4650682
  simp only [CollatzResearch.WordTrace]
  refine ⟨42406076934345215523846575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113082871824920574730257533 42406076934345215523846575)
  ·
    refine ⟨63609115401517823285769863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42406076934345215523846575 63609115401517823285769863)
    ·
      refine ⟨95413673102276734928654795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63609115401517823285769863 95413673102276734928654795)
      ·
        refine ⟨143120509653415102392982193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95413673102276734928654795 143120509653415102392982193)
        ·
          refine ⟨107340382240061326794736645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143120509653415102392982193 107340382240061326794736645)
          ·
            refine ⟨20126321670011498774013121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 107340382240061326794736645 20126321670011498774013121)
            ·
              refine ⟨15094741252508624080509841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20126321670011498774013121 15094741252508624080509841)
              ·
                refine ⟨11321055939381468060382381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15094741252508624080509841 11321055939381468060382381)
                ·
                  refine ⟨4245395977268050522643393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11321055939381468060382381 4245395977268050522643393)
                  ·
                    refine ⟨3184046982951037891982545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4245395977268050522643393 3184046982951037891982545)
                    ·
                      refine ⟨2388035237213278418986909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3184046982951037891982545 2388035237213278418986909)
                      ·
                        rfl

theorem cell23_4650682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 2, 3, 2, 2].length) (baseStart_4650682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4650682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4650682 prefixEnd_4650682 := by exact prefixLift 4650682
  have htrace : WordTrace (prefixWord ++ tailWord_4650682) baseStart_4650682 baseEnd_4650682 := by
    simpa [prefixWord, tailWord_4650682, baseEnd_4650682] using wordTrace_append hprefix tailTrace_4650682
  have hstable : (prefixWord ++ tailWord_4650682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4650682).length < 2 ^ (prefixWord ++ tailWord_4650682).sum := by decide
  have hdescent : baseEnd_4650682 < baseStart_4650682 := by decide
  rcases family_descends (prefixWord ++ tailWord_4650682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4650691 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 6]
def baseStart_4650691 : Nat := 118140960795 + 4650691 * 2 ^ 59
def prefixEnd_4650691 : Nat := 4983230072969 + 3 ^ 40 * 4650691 * 2
def baseEnd_4650691 : Nat := 2388039858539168883774367

theorem tailTrace_4650691 : CollatzResearch.WordTrace tailWord_4650691 prefixEnd_4650691 2388039858539168883774367 := by
  unfold tailWord_4650691
  simp only [CollatzResearch.WordTrace]
  refine ⟨169624635994348256632463927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113083090662898837754975951 169624635994348256632463927)
  ·
    refine ⟨254436953991522384948695891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169624635994348256632463927 254436953991522384948695891)
    ·
      refine ⟨381655430987283577423043837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254436953991522384948695891 381655430987283577423043837)
      ·
        refine ⟨143120786620231341533641439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 381655430987283577423043837 143120786620231341533641439)
        ·
          refine ⟨214681179930347012300462159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143120786620231341533641439 214681179930347012300462159)
          ·
            refine ⟨322021769895520518450693239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214681179930347012300462159 322021769895520518450693239)
            ·
              refine ⟨483032654843280777676039859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 322021769895520518450693239 483032654843280777676039859)
              ·
                refine ⟨724548982264921166514059789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 483032654843280777676039859 724548982264921166514059789)
                ·
                  refine ⟨271705868349345437442772421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 724548982264921166514059789 271705868349345437442772421)
                  ·
                    refine ⟨50944850315502269520519829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 271705868349345437442772421 50944850315502269520519829)
                    ·
                      refine ⟨2388039858539168883774367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50944850315502269520519829 2388039858539168883774367)
                      ·
                        rfl

theorem cell23_4650691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 6].length) (baseStart_4650691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4650691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4650691 prefixEnd_4650691 := by exact prefixLift 4650691
  have htrace : WordTrace (prefixWord ++ tailWord_4650691) baseStart_4650691 baseEnd_4650691 := by
    simpa [prefixWord, tailWord_4650691, baseEnd_4650691] using wordTrace_append hprefix tailTrace_4650691
  have hstable : (prefixWord ++ tailWord_4650691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4650691).length < 2 ^ (prefixWord ++ tailWord_4650691).sum := by decide
  have hdescent : baseEnd_4650691 < baseStart_4650691 := by decide
  rcases family_descends (prefixWord ++ tailWord_4650691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4650710 : List Nat := [5, 2, 1, 3, 1, 1, 3, 2, 1, 1, 3]
def baseStart_4650710 : Nat := 118140960795 + 4650710 * 2 ^ 59
def prefixEnd_4650710 : Nat := 4983230072969 + 3 ^ 40 * 4650710 * 2
def baseEnd_4650710 : Nat := 2388049614671604309436781

theorem tailTrace_4650710 : CollatzResearch.WordTrace tailWord_4650710 prefixEnd_4650710 2388049614671604309436781 := by
  unfold tailWord_4650710
  simp only [CollatzResearch.WordTrace]
  refine ⟨10601583061329963929837849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 113083552654186281918270389 10601583061329963929837849)
  ·
    refine ⟨7951187295997472947378387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10601583061329963929837849 7951187295997472947378387)
    ·
      refine ⟨11926780943996209421067581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7951187295997472947378387 11926780943996209421067581)
      ·
        refine ⟨4472542853998578532900343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11926780943996209421067581 4472542853998578532900343)
        ·
          refine ⟨6708814280997867799350515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4472542853998578532900343 6708814280997867799350515)
          ·
            refine ⟨10063221421496801699025773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6708814280997867799350515 10063221421496801699025773)
            ·
              refine ⟨3773708033061300637134665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10063221421496801699025773 3773708033061300637134665)
              ·
                refine ⟨2830281024795975477850999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3773708033061300637134665 2830281024795975477850999)
                ·
                  refine ⟨4245421537193963216776499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2830281024795975477850999 4245421537193963216776499)
                  ·
                    refine ⟨6368132305790944825164749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4245421537193963216776499 6368132305790944825164749)
                    ·
                      refine ⟨2388049614671604309436781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6368132305790944825164749 2388049614671604309436781)
                      ·
                        rfl

theorem cell23_4650710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_4650710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4650710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4650710 prefixEnd_4650710 := by exact prefixLift 4650710
  have htrace : WordTrace (prefixWord ++ tailWord_4650710) baseStart_4650710 baseEnd_4650710 := by
    simpa [prefixWord, tailWord_4650710, baseEnd_4650710] using wordTrace_append hprefix tailTrace_4650710
  have hstable : (prefixWord ++ tailWord_4650710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4650710).length < 2 ^ (prefixWord ++ tailWord_4650710).sum := by decide
  have hdescent : baseEnd_4650710 < baseStart_4650710 := by decide
  rcases family_descends (prefixWord ++ tailWord_4650710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4650755 : List Nat := [1, 1, 1, 3, 2, 2, 3, 1, 3, 4, 2]
def baseStart_4650755 : Nat := 118140960795 + 4650755 * 2 ^ 59
def prefixEnd_4650755 : Nat := 4983230072969 + 3 ^ 40 * 4650755 * 2
def baseEnd_4650755 : Nat := 2388072721301056633374073

theorem tailTrace_4650755 : CollatzResearch.WordTrace tailWord_4650755 prefixEnd_4650755 2388072721301056633374073 := by
  unfold tailWord_4650755
  simp only [CollatzResearch.WordTrace]
  refine ⟨169626970266116395562793719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113084646844077597041862479 169626970266116395562793719)
  ·
    refine ⟨254440455399174593344190579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169626970266116395562793719 254440455399174593344190579)
    ·
      refine ⟨381660683098761890016285869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254440455399174593344190579 381660683098761890016285869)
      ·
        refine ⟨143122756162035708756107201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 381660683098761890016285869 143122756162035708756107201)
        ·
          refine ⟨107342067121526781567080401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143122756162035708756107201 107342067121526781567080401)
          ·
            refine ⟨80506550341145086175310301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107342067121526781567080401 80506550341145086175310301)
            ·
              refine ⟨30189956377929407315741363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80506550341145086175310301 30189956377929407315741363)
              ·
                refine ⟨45284934566894110973612045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30189956377929407315741363 45284934566894110973612045)
                ·
                  refine ⟨16981850462585291615104517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45284934566894110973612045 16981850462585291615104517)
                  ·
                    refine ⟨3184096961734742177832097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16981850462585291615104517 3184096961734742177832097)
                    ·
                      refine ⟨2388072721301056633374073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3184096961734742177832097 2388072721301056633374073)
                      ·
                        rfl

theorem cell23_4650755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 3, 4, 2].length) (baseStart_4650755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4650755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4650755 prefixEnd_4650755 := by exact prefixLift 4650755
  have htrace : WordTrace (prefixWord ++ tailWord_4650755) baseStart_4650755 baseEnd_4650755 := by
    simpa [prefixWord, tailWord_4650755, baseEnd_4650755] using wordTrace_append hprefix tailTrace_4650755
  have hstable : (prefixWord ++ tailWord_4650755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4650755).length < 2 ^ (prefixWord ++ tailWord_4650755).sum := by decide
  have hdescent : baseEnd_4650755 < baseStart_4650755 := by decide
  rcases family_descends (prefixWord ++ tailWord_4650755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4650775 : List Nat := [1, 1, 3, 4, 2, 1, 1, 1, 2, 4, 3]
def baseStart_4650775 : Nat := 118140960795 + 4650775 * 2 ^ 59
def prefixEnd_4650775 : Nat := 4983230072969 + 3 ^ 40 * 4650775 * 2
def baseEnd_4650775 : Nat := 2388082990914146555123981

theorem tailTrace_4650775 : CollatzResearch.WordTrace tailWord_4650775 prefixEnd_4650775 2388082990914146555123981 := by
  unfold tailWord_4650775
  simp only [CollatzResearch.WordTrace]
  refine ⟨169627699726043938978521779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113085133150695959319014519 169627699726043938978521779)
  ·
    refine ⟨254441549589065908467782669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169627699726043938978521779 254441549589065908467782669)
    ·
      refine ⟨95415581095899715675418501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 254441549589065908467782669 95415581095899715675418501)
      ·
        refine ⟨17890421455481196689140969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95415581095899715675418501 17890421455481196689140969)
        ·
          refine ⟨13417816091610897516855727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17890421455481196689140969 13417816091610897516855727)
          ·
            refine ⟨20126724137416346275283591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13417816091610897516855727 20126724137416346275283591)
            ·
              refine ⟨30190086206124519412925387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20126724137416346275283591 30190086206124519412925387)
              ·
                refine ⟨45285129309186779119388081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30190086206124519412925387 45285129309186779119388081)
                ·
                  refine ⟨33963846981890084339541061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45285129309186779119388081 33963846981890084339541061)
                  ·
                    refine ⟨6368221309104390813663949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33963846981890084339541061 6368221309104390813663949)
                    ·
                      refine ⟨2388082990914146555123981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6368221309104390813663949 2388082990914146555123981)
                      ·
                        rfl

theorem cell23_4650775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_4650775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4650775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4650775 prefixEnd_4650775 := by exact prefixLift 4650775
  have htrace : WordTrace (prefixWord ++ tailWord_4650775) baseStart_4650775 baseEnd_4650775 := by
    simpa [prefixWord, tailWord_4650775, baseEnd_4650775] using wordTrace_append hprefix tailTrace_4650775
  have hstable : (prefixWord ++ tailWord_4650775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4650775).length < 2 ^ (prefixWord ++ tailWord_4650775).sum := by decide
  have hdescent : baseEnd_4650775 < baseStart_4650775 := by decide
  rcases family_descends (prefixWord ++ tailWord_4650775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4650785 : List Nat := [1, 2, 3, 2, 1, 4, 1, 1, 2, 2, 4]
def baseStart_4650785 : Nat := 118140960795 + 4650785 * 2 ^ 59
def prefixEnd_4650785 : Nat := 4983230072969 + 3 ^ 40 * 4650785 * 2
def baseEnd_4650785 : Nat := 2388088125720691515998935

theorem tailTrace_4650785 : CollatzResearch.WordTrace tailWord_4650785 prefixEnd_4650785 2388088125720691515998935 := by
  unfold tailWord_4650785
  simp only [CollatzResearch.WordTrace]
  refine ⟨169628064456007710686385809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113085376304005140457590539 169628064456007710686385809)
  ·
    refine ⟨127221048342005783014789357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169628064456007710686385809 127221048342005783014789357)
    ·
      refine ⟨47707893128252168630546009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127221048342005783014789357 47707893128252168630546009)
      ·
        refine ⟨35780919846189126472909507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47707893128252168630546009 35780919846189126472909507)
        ·
          refine ⟨53671379769283689709364261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35780919846189126472909507 53671379769283689709364261)
          ·
            refine ⟨10063383706740691820505799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53671379769283689709364261 10063383706740691820505799)
            ·
              refine ⟨15095075560111037730758699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10063383706740691820505799 15095075560111037730758699)
              ·
                refine ⟨22642613340166556596138049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15095075560111037730758699 22642613340166556596138049)
                ·
                  refine ⟨16981960005124917447103537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22642613340166556596138049 16981960005124917447103537)
                  ·
                    refine ⟨12736470003843688085327653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16981960005124917447103537 12736470003843688085327653)
                    ·
                      refine ⟨2388088125720691515998935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12736470003843688085327653 2388088125720691515998935)
                      ·
                        rfl

theorem cell23_4650785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_4650785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4650785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4650785 prefixEnd_4650785 := by exact prefixLift 4650785
  have htrace : WordTrace (prefixWord ++ tailWord_4650785) baseStart_4650785 baseEnd_4650785 := by
    simpa [prefixWord, tailWord_4650785, baseEnd_4650785] using wordTrace_append hprefix tailTrace_4650785
  have hstable : (prefixWord ++ tailWord_4650785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4650785).length < 2 ^ (prefixWord ++ tailWord_4650785).sum := by decide
  have hdescent : baseEnd_4650785 < baseStart_4650785 := by decide
  rcases family_descends (prefixWord ++ tailWord_4650785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4650789 : List Nat := [1, 3, 1, 2, 3, 2, 2, 3, 2, 2, 2]
def baseStart_4650789 : Nat := 118140960795 + 4650789 * 2 ^ 59
def prefixEnd_4650789 : Nat := 4983230072969 + 3 ^ 40 * 4650789 * 2
def baseEnd_4650789 : Nat := 2388090179643309500348917

theorem tailTrace_4650789 : CollatzResearch.WordTrace tailWord_4650789 prefixEnd_4650789 2388090179643309500348917 := by
  unfold tailWord_4650789
  simp only [CollatzResearch.WordTrace]
  refine ⟨169628210347993219369531421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113085473565328812913020947 169628210347993219369531421)
  ·
    refine ⟨63610578880497457263574283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169628210347993219369531421 63610578880497457263574283)
    ·
      refine ⟨95415868320746185895361425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63610578880497457263574283 95415868320746185895361425)
      ·
        refine ⟨71561901240559639421521069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95415868320746185895361425 71561901240559639421521069)
        ·
          refine ⟨26835712965209864783070401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71561901240559639421521069 26835712965209864783070401)
          ·
            refine ⟨20126784723907398587302801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26835712965209864783070401 20126784723907398587302801)
            ·
              refine ⟨15095088542930548940477101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20126784723907398587302801 15095088542930548940477101)
              ·
                refine ⟨5660658203598955852678913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15095088542930548940477101 5660658203598955852678913)
                ·
                  refine ⟨4245493652699216889509185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5660658203598955852678913 4245493652699216889509185)
                  ·
                    refine ⟨3184120239524412667131889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4245493652699216889509185 3184120239524412667131889)
                    ·
                      refine ⟨2388090179643309500348917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3184120239524412667131889 2388090179643309500348917)
                      ·
                        rfl

theorem cell23_4650789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 3, 2, 2, 2].length) (baseStart_4650789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4650789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4650789 prefixEnd_4650789 := by exact prefixLift 4650789
  have htrace : WordTrace (prefixWord ++ tailWord_4650789) baseStart_4650789 baseEnd_4650789 := by
    simpa [prefixWord, tailWord_4650789, baseEnd_4650789] using wordTrace_append hprefix tailTrace_4650789
  have hstable : (prefixWord ++ tailWord_4650789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4650789).length < 2 ^ (prefixWord ++ tailWord_4650789).sum := by decide
  have hdescent : baseEnd_4650789 < baseStart_4650789 := by decide
  rcases family_descends (prefixWord ++ tailWord_4650789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4650829 : List Nat := [1, 6, 1, 2, 1, 1, 2, 4, 5]
def baseStart_4650829 : Nat := 118140960795 + 4650829 * 2 ^ 59
def prefixEnd_4650829 : Nat := 4983230072969 + 3 ^ 40 * 4650829 * 2
def baseEnd_4650829 : Nat := 265345635429943260427637

theorem tailTrace_4650829 : CollatzResearch.WordTrace tailWord_4650829 prefixEnd_4650829 265345635429943260427637 := by
  unfold tailWord_4650829
  simp only [CollatzResearch.WordTrace]
  refine ⟨169629669267848306200987541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113086446178565537467325027 169629669267848306200987541)
  ·
    refine ⟨7951390746930389353171291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 169629669267848306200987541 7951390746930389353171291)
    ·
      refine ⟨11927086120395584029756937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7951390746930389353171291 11927086120395584029756937)
      ·
        refine ⟨8945314590296688022317703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11927086120395584029756937 8945314590296688022317703)
        ·
          refine ⟨13417971885445032033476555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8945314590296688022317703 13417971885445032033476555)
          ·
            refine ⟨20126957828167548050214833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13417971885445032033476555 20126957828167548050214833)
            ·
              refine ⟨15095218371125661037661125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20126957828167548050214833 15095218371125661037661125)
              ·
                refine ⟨2830353444586061444561461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15095218371125661037661125 2830353444586061444561461)
                ·
                  refine ⟨265345635429943260427637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2830353444586061444561461 265345635429943260427637)
                  ·
                    rfl

theorem cell23_4650829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_4650829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4650829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4650829 prefixEnd_4650829 := by exact prefixLift 4650829
  have htrace : WordTrace (prefixWord ++ tailWord_4650829) baseStart_4650829 baseEnd_4650829 := by
    simpa [prefixWord, tailWord_4650829, baseEnd_4650829] using wordTrace_append hprefix tailTrace_4650829
  have hstable : (prefixWord ++ tailWord_4650829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4650829).length < 2 ^ (prefixWord ++ tailWord_4650829).sum := by decide
  have hdescent : baseEnd_4650829 < baseStart_4650829 := by decide
  rcases family_descends (prefixWord ++ tailWord_4650829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4650862 : List Nat := [4, 1, 2, 3, 1, 1, 2, 1, 1, 3, 4]
def baseStart_4650862 : Nat := 118140960795 + 4650862 * 2 ^ 59
def prefixEnd_4650862 : Nat := 4983230072969 + 3 ^ 40 * 4650862 * 2
def baseEnd_4650862 : Nat := 2388127663731087714736081

theorem tailTrace_4650862 : CollatzResearch.WordTrace tailWord_4650862 prefixEnd_4650862 2388127663731087714736081 := by
  unfold tailWord_4650862
  simp only [CollatzResearch.WordTrace]
  refine ⟨21203859109591094104617355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113087248584485835224625893 21203859109591094104617355)
  ·
    refine ⟨31805788664386641156926033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21203859109591094104617355 31805788664386641156926033)
    ·
      refine ⟨23854341498289980867694525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31805788664386641156926033 23854341498289980867694525)
      ·
        refine ⟨8945378061858742825385447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23854341498289980867694525 8945378061858742825385447)
        ·
          refine ⟨13418067092788114238078171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8945378061858742825385447 13418067092788114238078171)
          ·
            refine ⟨20127100639182171357117257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13418067092788114238078171 20127100639182171357117257)
            ·
              refine ⟨15095325479386628517837943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20127100639182171357117257 15095325479386628517837943)
              ·
                refine ⟨22642988219079942776756915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15095325479386628517837943 22642988219079942776756915)
                ·
                  refine ⟨33964482328619914165135373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22642988219079942776756915 33964482328619914165135373)
                  ·
                    refine ⟨12736680873232467811925765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33964482328619914165135373 12736680873232467811925765)
                    ·
                      refine ⟨2388127663731087714736081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12736680873232467811925765 2388127663731087714736081)
                      ·
                        rfl

theorem cell23_4650862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_4650862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4650862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4650862 prefixEnd_4650862 := by exact prefixLift 4650862
  have htrace : WordTrace (prefixWord ++ tailWord_4650862) baseStart_4650862 baseEnd_4650862 := by
    simpa [prefixWord, tailWord_4650862, baseEnd_4650862] using wordTrace_append hprefix tailTrace_4650862
  have hstable : (prefixWord ++ tailWord_4650862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4650862).length < 2 ^ (prefixWord ++ tailWord_4650862).sum := by decide
  have hdescent : baseEnd_4650862 < baseStart_4650862 := by decide
  rcases family_descends (prefixWord ++ tailWord_4650862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4650865 : List Nat := [1, 2, 2, 2, 1, 3, 1, 3, 1, 4, 3]
def baseStart_4650865 : Nat := 118140960795 + 4650865 * 2 ^ 59
def prefixEnd_4650865 : Nat := 4983230072969 + 3 ^ 40 * 4650865 * 2
def baseEnd_4650865 : Nat := 2388129204173051202998567

theorem tailTrace_4650865 : CollatzResearch.WordTrace tailWord_4650865 prefixEnd_4650865 2388129204173051202998567 := by
  unfold tailWord_4650865
  simp only [CollatzResearch.WordTrace]
  refine ⟨169630982295717884349298049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113087321530478589566198699 169630982295717884349298049)
  ·
    refine ⟨127223236721788413261973537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169630982295717884349298049 127223236721788413261973537)
    ·
      refine ⟨95417427541341309946480153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127223236721788413261973537 95417427541341309946480153)
      ·
        refine ⟨71563070656005982459860115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95417427541341309946480153 71563070656005982459860115)
        ·
          refine ⟨107344605984008973689790173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71563070656005982459860115 107344605984008973689790173)
          ·
            refine ⟨40254227244003365133671315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107344605984008973689790173 40254227244003365133671315)
            ·
              refine ⟨60381340866005047700506973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40254227244003365133671315 60381340866005047700506973)
              ·
                refine ⟨22643002824751892887690115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60381340866005047700506973 22643002824751892887690115)
                ·
                  refine ⟨33964504237127839331535173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22643002824751892887690115 33964504237127839331535173)
                  ·
                    refine ⟨6368344544461469874662845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33964504237127839331535173 6368344544461469874662845)
                    ·
                      refine ⟨2388129204173051202998567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6368344544461469874662845 2388129204173051202998567)
                      ·
                        rfl

theorem cell23_4650865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 4, 3].length) (baseStart_4650865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4650865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4650865 prefixEnd_4650865 := by exact prefixLift 4650865
  have htrace : WordTrace (prefixWord ++ tailWord_4650865) baseStart_4650865 baseEnd_4650865 := by
    simpa [prefixWord, tailWord_4650865, baseEnd_4650865] using wordTrace_append hprefix tailTrace_4650865
  have hstable : (prefixWord ++ tailWord_4650865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4650865).length < 2 ^ (prefixWord ++ tailWord_4650865).sum := by decide
  have hdescent : baseEnd_4650865 < baseStart_4650865 := by decide
  rcases family_descends (prefixWord ++ tailWord_4650865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4650885 : List Nat := [1, 3, 1, 1, 3, 2, 2, 4, 6]
def baseStart_4650885 : Nat := 118140960795 + 4650885 * 2 ^ 59
def prefixEnd_4650885 : Nat := 4983230072969 + 3 ^ 40 * 4650885 * 2
def baseEnd_4650885 : Nat := 265348830420682347194275

theorem tailTrace_4650885 : CollatzResearch.WordTrace tailWord_4650885 prefixEnd_4650885 265348830420682347194275 := by
  unfold tailWord_4650885
  simp only [CollatzResearch.WordTrace]
  refine ⟨169631711755645427765026109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113087807837096951843350739 169631711755645427765026109)
  ·
    refine ⟨63611891908367035411884791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169631711755645427765026109 63611891908367035411884791)
    ·
      refine ⟨95417837862550553117827187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63611891908367035411884791 95417837862550553117827187)
      ·
        refine ⟨143126756793825829676740781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95417837862550553117827187 143126756793825829676740781)
        ·
          refine ⟨53672533797684686128777793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 143126756793825829676740781 53672533797684686128777793)
          ·
            refine ⟨40254400348263514596583345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53672533797684686128777793 40254400348263514596583345)
            ·
              refine ⟨30190800261197635947437509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40254400348263514596583345 30190800261197635947437509)
              ·
                refine ⟨5660775048974556740144533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30190800261197635947437509 5660775048974556740144533)
                ·
                  refine ⟨265348830420682347194275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5660775048974556740144533 265348830420682347194275)
                  ·
                    rfl

theorem cell23_4650885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 4, 6].length) (baseStart_4650885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4650885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4650885 prefixEnd_4650885 := by exact prefixLift 4650885
  have htrace : WordTrace (prefixWord ++ tailWord_4650885) baseStart_4650885 baseEnd_4650885 := by
    simpa [prefixWord, tailWord_4650885, baseEnd_4650885] using wordTrace_append hprefix tailTrace_4650885
  have hstable : (prefixWord ++ tailWord_4650885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4650885).length < 2 ^ (prefixWord ++ tailWord_4650885).sum := by decide
  have hdescent : baseEnd_4650885 < baseStart_4650885 := by decide
  rcases family_descends (prefixWord ++ tailWord_4650885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4650912 : List Nat := [2, 1, 1, 4, 1, 1, 1, 3, 5, 1, 3]
def baseStart_4650912 : Nat := 118140960795 + 4650912 * 2 ^ 59
def prefixEnd_4650912 : Nat := 4983230072969 + 3 ^ 40 * 4650912 * 2
def baseEnd_4650912 : Nat := 2388153337763812519110851

theorem tailTrace_4650912 : CollatzResearch.WordTrace tailWord_4650912 prefixEnd_4650912 2388153337763812519110851 := by
  unfold tailWord_4650912
  simp only [CollatzResearch.WordTrace]
  refine ⟨84816348263273805688129495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113088464351031740917505993 84816348263273805688129495)
  ·
    refine ⟨127224522394910708532194243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84816348263273805688129495 127224522394910708532194243)
    ·
      refine ⟨190836783592366062798291365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127224522394910708532194243 190836783592366062798291365)
      ·
        refine ⟨35781896923568636774679631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 190836783592366062798291365 35781896923568636774679631)
        ·
          refine ⟨53672845385352955162019447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35781896923568636774679631 53672845385352955162019447)
          ·
            refine ⟨80509268078029432743029171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53672845385352955162019447 80509268078029432743029171)
            ·
              refine ⟨120763902117044149114543757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80509268078029432743029171 120763902117044149114543757)
              ·
                refine ⟨45286463293891555917953909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120763902117044149114543757 45286463293891555917953909)
                ·
                  refine ⟨4245605933802333367308179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45286463293891555917953909 4245605933802333367308179)
                  ·
                    refine ⟨6368408900703500050962269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4245605933802333367308179 6368408900703500050962269)
                    ·
                      refine ⟨2388153337763812519110851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6368408900703500050962269 2388153337763812519110851)
                      ·
                        rfl

theorem cell23_4650912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 5, 1, 3].length) (baseStart_4650912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4650912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4650912 prefixEnd_4650912 := by exact prefixLift 4650912
  have htrace : WordTrace (prefixWord ++ tailWord_4650912) baseStart_4650912 baseEnd_4650912 := by
    simpa [prefixWord, tailWord_4650912, baseEnd_4650912] using wordTrace_append hprefix tailTrace_4650912
  have hstable : (prefixWord ++ tailWord_4650912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4650912).length < 2 ^ (prefixWord ++ tailWord_4650912).sum := by decide
  have hdescent : baseEnd_4650912 < baseStart_4650912 := by decide
  rcases family_descends (prefixWord ++ tailWord_4650912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4650940 : List Nat := [2, 2, 2, 5, 1, 2, 2, 2, 1, 4]
def baseStart_4650940 : Nat := 118140960795 + 4650940 * 2 ^ 59
def prefixEnd_4650940 : Nat := 4983230072969 + 3 ^ 40 * 4650940 * 2
def baseEnd_4650940 : Nat := 796055905074046136520241

theorem tailTrace_4650940 : CollatzResearch.WordTrace tailWord_4650940 prefixEnd_4650940 796055905074046136520241 := by
  unfold tailWord_4650940
  simp only [CollatzResearch.WordTrace]
  refine ⟨84816858885223086079139137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113089145180297448105518849 84816858885223086079139137)
  ·
    refine ⟨63612644163917314559354353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84816858885223086079139137 63612644163917314559354353)
    ·
      refine ⟨47709483122937985919515765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63612644163917314559354353 47709483122937985919515765)
      ·
        refine ⟨4472764042775436179954603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47709483122937985919515765 4472764042775436179954603)
        ·
          refine ⟨6709146064163154269931905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4472764042775436179954603 6709146064163154269931905)
          ·
            refine ⟨5031859548122365702448929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6709146064163154269931905 5031859548122365702448929)
            ·
              refine ⟨3773894661091774276836697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5031859548122365702448929 3773894661091774276836697)
              ·
                refine ⟨2830420995818830707627523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3773894661091774276836697 2830420995818830707627523)
                ·
                  refine ⟨4245631493728246061441285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2830420995818830707627523 4245631493728246061441285)
                  ·
                    refine ⟨796055905074046136520241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4245631493728246061441285 796055905074046136520241)
                    ·
                      rfl

theorem cell23_4650940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 2, 2, 1, 4].length) (baseStart_4650940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4650940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4650940 prefixEnd_4650940 := by exact prefixLift 4650940
  have htrace : WordTrace (prefixWord ++ tailWord_4650940) baseStart_4650940 baseEnd_4650940 := by
    simpa [prefixWord, tailWord_4650940, baseEnd_4650940] using wordTrace_append hprefix tailTrace_4650940
  have hstable : (prefixWord ++ tailWord_4650940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4650940).length < 2 ^ (prefixWord ++ tailWord_4650940).sum := by decide
  have hdescent : baseEnd_4650940 < baseStart_4650940 := by decide
  rcases family_descends (prefixWord ++ tailWord_4650940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4650952 : List Nat := [2, 1, 3, 1, 4, 1, 1, 2, 3, 1, 4]
def baseStart_4650952 : Nat := 118140960795 + 4650952 * 2 ^ 59
def prefixEnd_4650952 : Nat := 4983230072969 + 3 ^ 40 * 4650952 * 2
def baseEnd_4650952 : Nat := 2388173876989992362610667

theorem tailTrace_4650952 : CollatzResearch.WordTrace tailWord_4650952 prefixEnd_4650952 2388173876989992362610667 := by
  unfold tailWord_4650952
  simp only [CollatzResearch.WordTrace]
  refine ⟨84817077723201349103857555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113089436964268465471810073 84817077723201349103857555)
  ·
    refine ⟨127225616584802023655786333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84817077723201349103857555 127225616584802023655786333)
    ·
      refine ⟨47709606219300758870919875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127225616584802023655786333 47709606219300758870919875)
      ·
        refine ⟨71564409328951138306379813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47709606219300758870919875 71564409328951138306379813)
        ·
          refine ⟨13418326749178338432446215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71564409328951138306379813 13418326749178338432446215)
          ·
            refine ⟨20127490123767507648669323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13418326749178338432446215 20127490123767507648669323)
            ·
              refine ⟨30191235185651261473003985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20127490123767507648669323 30191235185651261473003985)
              ·
                refine ⟨22643426389238446104752989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30191235185651261473003985 22643426389238446104752989)
                ·
                  refine ⟨8491284895964417289282371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22643426389238446104752989 8491284895964417289282371)
                  ·
                    refine ⟨12736927343946625933923557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8491284895964417289282371 12736927343946625933923557)
                    ·
                      refine ⟨2388173876989992362610667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12736927343946625933923557 2388173876989992362610667)
                      ·
                        rfl

theorem cell23_4650952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 3, 1, 4].length) (baseStart_4650952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4650952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4650952 prefixEnd_4650952 := by exact prefixLift 4650952
  have htrace : WordTrace (prefixWord ++ tailWord_4650952) baseStart_4650952 baseEnd_4650952 := by
    simpa [prefixWord, tailWord_4650952, baseEnd_4650952] using wordTrace_append hprefix tailTrace_4650952
  have hstable : (prefixWord ++ tailWord_4650952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4650952).length < 2 ^ (prefixWord ++ tailWord_4650952).sum := by decide
  have hdescent : baseEnd_4650952 < baseStart_4650952 := by decide
  rcases family_descends (prefixWord ++ tailWord_4650952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4650955 : List Nat := [1, 1, 1, 1, 3, 4, 2, 1, 3, 1, 5]
def baseStart_4650955 : Nat := 118140960795 + 4650955 * 2 ^ 59
def prefixEnd_4650955 : Nat := 4983230072969 + 3 ^ 40 * 4650955 * 2
def baseEnd_4650955 : Nat := 2388175417431955850873153

theorem tailTrace_4650955 : CollatzResearch.WordTrace tailWord_4650955 prefixEnd_4650955 2388175417431955850873153 := by
  unfold tailWord_4650955
  simp only [CollatzResearch.WordTrace]
  refine ⟨169634264865391829720074319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113089509910261219813382879 169634264865391829720074319)
  ·
    refine ⟨254451397298087744580111479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169634264865391829720074319 254451397298087744580111479)
    ·
      refine ⟨381677095947131616870167219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254451397298087744580111479 381677095947131616870167219)
      ·
        refine ⟨572515643920697425305250829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 381677095947131616870167219 572515643920697425305250829)
        ·
          refine ⟨214693366470261534489469061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 572515643920697425305250829 214693366470261534489469061)
          ·
            refine ⟨40255006213174037716775449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 214693366470261534489469061 40255006213174037716775449)
            ·
              refine ⟨30191254659880528287581587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40255006213174037716775449 30191254659880528287581587)
              ·
                refine ⟨45286881989820792431372381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30191254659880528287581587 45286881989820792431372381)
                ·
                  refine ⟨16982580746182797161764643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45286881989820792431372381 16982580746182797161764643)
                  ·
                    refine ⟨25473871119274195742646965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16982580746182797161764643 25473871119274195742646965)
                    ·
                      refine ⟨2388175417431955850873153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25473871119274195742646965 2388175417431955850873153)
                      ·
                        rfl

theorem cell23_4650955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 3, 1, 5].length) (baseStart_4650955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4650955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4650955 prefixEnd_4650955 := by exact prefixLift 4650955
  have htrace : WordTrace (prefixWord ++ tailWord_4650955) baseStart_4650955 baseEnd_4650955 := by
    simpa [prefixWord, tailWord_4650955, baseEnd_4650955] using wordTrace_append hprefix tailTrace_4650955
  have hstable : (prefixWord ++ tailWord_4650955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4650955).length < 2 ^ (prefixWord ++ tailWord_4650955).sum := by decide
  have hdescent : baseEnd_4650955 < baseStart_4650955 := by decide
  rcases family_descends (prefixWord ++ tailWord_4650955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4650973 : List Nat := [1, 4, 3, 1, 3, 2, 1, 1, 2, 3, 2]
def baseStart_4650973 : Nat := 118140960795 + 4650973 * 2 ^ 59
def prefixEnd_4650973 : Nat := 4983230072969 + 3 ^ 40 * 4650973 * 2
def baseEnd_4650973 : Nat := 2388184660083736780448071

theorem tailTrace_4650973 : CollatzResearch.WordTrace tailWord_4650973 prefixEnd_4650973 2388184660083736780448071 := by
  unfold tailWord_4650973
  simp only [CollatzResearch.WordTrace]
  refine ⟨169634921379326618794229573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113089947586217745862819715 169634921379326618794229573)
  ·
    refine ⟨31806547758623741023918045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 169634921379326618794229573 31806547758623741023918045)
    ·
      refine ⟨11927455409483902883969267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31806547758623741023918045 11927455409483902883969267)
      ·
        refine ⟨17891183114225854325953901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11927455409483902883969267 17891183114225854325953901)
        ·
          refine ⟨6709193667834695372232713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17891183114225854325953901 6709193667834695372232713)
          ·
            refine ⟨5031895250876021529174535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6709193667834695372232713 5031895250876021529174535)
            ·
              refine ⟨7547842876314032293761803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5031895250876021529174535 7547842876314032293761803)
              ·
                refine ⟨11321764314471048440642705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7547842876314032293761803 11321764314471048440642705)
                ·
                  refine ⟨8491323235853286330482029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11321764314471048440642705 8491323235853286330482029)
                  ·
                    refine ⟨3184246213444982373930761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8491323235853286330482029 3184246213444982373930761)
                    ·
                      refine ⟨2388184660083736780448071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3184246213444982373930761 2388184660083736780448071)
                      ·
                        rfl

theorem cell23_4650973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 1, 2, 3, 2].length) (baseStart_4650973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4650973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4650973 prefixEnd_4650973 := by exact prefixLift 4650973
  have htrace : WordTrace (prefixWord ++ tailWord_4650973) baseStart_4650973 baseEnd_4650973 := by
    simpa [prefixWord, tailWord_4650973, baseEnd_4650973] using wordTrace_append hprefix tailTrace_4650973
  have hstable : (prefixWord ++ tailWord_4650973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4650973).length < 2 ^ (prefixWord ++ tailWord_4650973).sum := by decide
  have hdescent : baseEnd_4650973 < baseStart_4650973 := by decide
  rcases family_descends (prefixWord ++ tailWord_4650973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4650983 : List Nat := [1, 1, 5, 2, 4, 1, 2, 1, 1, 5]
def baseStart_4650983 : Nat := 118140960795 + 4650983 * 2 ^ 59
def prefixEnd_4650983 : Nat := 4983230072969 + 3 ^ 40 * 4650983 * 2
def baseEnd_4650983 : Nat := 796063264963427247107675

theorem tailTrace_4650983 : CollatzResearch.WordTrace tailWord_4650983 prefixEnd_4650983 796063264963427247107675 := by
  unfold tailWord_4650983
  simp only [CollatzResearch.WordTrace]
  refine ⟨169635286109290390502093603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113090190739526927001395735 169635286109290390502093603)
  ·
    refine ⟨254452929163935585753140405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169635286109290390502093603 254452929163935585753140405)
    ·
      refine ⟨23854962109118961164356913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 254452929163935585753140405 23854962109118961164356913)
      ·
        refine ⟨17891221581839220873267685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23854962109118961164356913 17891221581839220873267685)
        ·
          refine ⟨3354604046594853913737691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17891221581839220873267685 3354604046594853913737691)
          ·
            refine ⟨5031906069892280870606537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3354604046594853913737691 5031906069892280870606537)
            ·
              refine ⟨3773929552419210652954903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5031906069892280870606537 3773929552419210652954903)
              ·
                refine ⟨5660894328628815979432355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3773929552419210652954903 5660894328628815979432355)
                ·
                  refine ⟨8491341492943223969148533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5660894328628815979432355 8491341492943223969148533)
                  ·
                    refine ⟨796063264963427247107675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8491341492943223969148533 796063264963427247107675)
                    ·
                      rfl

theorem cell23_4650983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 2, 1, 1, 5].length) (baseStart_4650983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4650983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4650983 prefixEnd_4650983 := by exact prefixLift 4650983
  have htrace : WordTrace (prefixWord ++ tailWord_4650983) baseStart_4650983 baseEnd_4650983 := by
    simpa [prefixWord, tailWord_4650983, baseEnd_4650983] using wordTrace_append hprefix tailTrace_4650983
  have hstable : (prefixWord ++ tailWord_4650983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4650983).length < 2 ^ (prefixWord ++ tailWord_4650983).sum := by decide
  have hdescent : baseEnd_4650983 < baseStart_4650983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4650983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4651005 : List Nat := [1, 4, 1, 1, 1, 2, 2, 1, 1, 9]
def baseStart_4651005 : Nat := 118140960795 + 4651005 * 2 ^ 59
def prefixEnd_4651005 : Nat := 4983230072969 + 3 ^ 40 * 4651005 * 2
def baseEnd_4651005 : Nat := 796067030488226885082641

theorem tailTrace_4651005 : CollatzResearch.WordTrace tailWord_4651005 prefixEnd_4651005 796067030488226885082641 := by
  unfold tailWord_4651005
  simp only [CollatzResearch.WordTrace]
  refine ⟨169636088515210688259394469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113090725676807125506262979 169636088515210688259394469)
  ·
    refine ⟨31806766596602004048636463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 169636088515210688259394469 31806766596602004048636463)
    ·
      refine ⟨47710149894903006072954695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31806766596602004048636463 47710149894903006072954695)
      ·
        refine ⟨71565224842354509109432043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47710149894903006072954695 71565224842354509109432043)
        ·
          refine ⟨107347837263531763664148065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71565224842354509109432043 107347837263531763664148065)
          ·
            refine ⟨80510877947648822748111049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107347837263531763664148065 80510877947648822748111049)
            ·
              refine ⟨60383158460736617061083287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80510877947648822748111049 60383158460736617061083287)
              ·
                refine ⟨90574737691104925591624931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60383158460736617061083287 90574737691104925591624931)
                ·
                  refine ⟨135862106536657388387437397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90574737691104925591624931 135862106536657388387437397)
                  ·
                    refine ⟨796067030488226885082641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 135862106536657388387437397 796067030488226885082641)
                    ·
                      rfl

theorem cell23_4651005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 9].length) (baseStart_4651005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4651005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4651005 prefixEnd_4651005 := by exact prefixLift 4651005
  have htrace : WordTrace (prefixWord ++ tailWord_4651005) baseStart_4651005 baseEnd_4651005 := by
    simpa [prefixWord, tailWord_4651005, baseEnd_4651005] using wordTrace_append hprefix tailTrace_4651005
  have hstable : (prefixWord ++ tailWord_4651005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4651005).length < 2 ^ (prefixWord ++ tailWord_4651005).sum := by decide
  have hdescent : baseEnd_4651005 < baseStart_4651005 := by decide
  rcases family_descends (prefixWord ++ tailWord_4651005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4651035 : List Nat := [1, 1, 1, 1, 1, 1, 3, 4, 4, 6]
def baseStart_4651035 : Nat := 118140960795 + 4651035 * 2 ^ 59
def prefixEnd_4651035 : Nat := 4983230072969 + 3 ^ 40 * 4651035 * 2
def baseEnd_4651035 : Nat := 796072165294771845957595

theorem tailTrace_4651035 : CollatzResearch.WordTrace tailWord_4651035 prefixEnd_4651035 796072165294771845957595 := by
  unfold tailWord_4651035
  simp only [CollatzResearch.WordTrace]
  refine ⟨169637182705102003382986559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113091455136734668921991039 169637182705102003382986559)
  ·
    refine ⟨254455774057653005074479839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169637182705102003382986559 254455774057653005074479839)
    ·
      refine ⟨381683661086479507611719759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254455774057653005074479839 381683661086479507611719759)
      ·
        refine ⟨572525491629719261417579639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 381683661086479507611719759 572525491629719261417579639)
        ·
          refine ⟨858788237444578892126369459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 572525491629719261417579639 858788237444578892126369459)
          ·
            refine ⟨1288182356166868338189554189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 858788237444578892126369459 1288182356166868338189554189)
            ·
              refine ⟨483068383562575626821082821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1288182356166868338189554189 483068383562575626821082821)
              ·
                refine ⟨90575321917982930028953029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 483068383562575626821082821 90575321917982930028953029)
                ·
                  refine ⟨16982872859621799380428693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 90575321917982930028953029 16982872859621799380428693)
                  ·
                    refine ⟨796072165294771845957595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16982872859621799380428693 796072165294771845957595)
                    ·
                      rfl

theorem cell23_4651035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 6].length) (baseStart_4651035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4651035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4651035 prefixEnd_4651035 := by exact prefixLift 4651035
  have htrace : WordTrace (prefixWord ++ tailWord_4651035) baseStart_4651035 baseEnd_4651035 := by
    simpa [prefixWord, tailWord_4651035, baseEnd_4651035] using wordTrace_append hprefix tailTrace_4651035
  have hstable : (prefixWord ++ tailWord_4651035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4651035).length < 2 ^ (prefixWord ++ tailWord_4651035).sum := by decide
  have hdescent : baseEnd_4651035 < baseStart_4651035 := by decide
  rcases family_descends (prefixWord ++ tailWord_4651035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4651055 : List Nat := [1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 6]
def baseStart_4651055 : Nat := 118140960795 + 4651055 * 2 ^ 59
def prefixEnd_4651055 : Nat := 4983230072969 + 3 ^ 40 * 4651055 * 2
def baseEnd_4651055 : Nat := 2388226765497405459622693

theorem tailTrace_4651055 : CollatzResearch.WordTrace tailWord_4651055 prefixEnd_4651055 2388226765497405459622693 := by
  unfold tailWord_4651055
  simp only [CollatzResearch.WordTrace]
  refine ⟨169637912165029546798714619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113091941443353031199143079 169637912165029546798714619)
  ·
    refine ⟨254456868247544320198071929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169637912165029546798714619 254456868247544320198071929)
    ·
      refine ⟨190842651185658240148553947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 254456868247544320198071929 190842651185658240148553947)
      ·
        refine ⟨286263976778487360222830921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190842651185658240148553947 286263976778487360222830921)
        ·
          refine ⟨214697982583865520167123191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 286263976778487360222830921 214697982583865520167123191)
          ·
            refine ⟨322046973875798280250684787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214697982583865520167123191 322046973875798280250684787)
            ·
              refine ⟨483070460813697420376027181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 322046973875798280250684787 483070460813697420376027181)
              ·
                refine ⟨181151422805136532641010193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 483070460813697420376027181 181151422805136532641010193)
                ·
                  refine ⟨135863567103852399480757645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 181151422805136532641010193 135863567103852399480757645)
                  ·
                    refine ⟨50948837663944649805284117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 135863567103852399480757645 50948837663944649805284117)
                    ·
                      refine ⟨2388226765497405459622693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50948837663944649805284117 2388226765497405459622693)
                      ·
                        rfl

theorem cell23_4651055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 6].length) (baseStart_4651055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4651055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4651055 prefixEnd_4651055 := by exact prefixLift 4651055
  have htrace : WordTrace (prefixWord ++ tailWord_4651055) baseStart_4651055 baseEnd_4651055 := by
    simpa [prefixWord, tailWord_4651055, baseEnd_4651055] using wordTrace_append hprefix tailTrace_4651055
  have hstable : (prefixWord ++ tailWord_4651055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4651055).length < 2 ^ (prefixWord ++ tailWord_4651055).sum := by decide
  have hdescent : baseEnd_4651055 < baseStart_4651055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4651055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4651116 : List Nat := [2, 2, 1, 1, 3, 3, 4, 2, 5]
def baseStart_4651116 : Nat := 118140960795 + 4651116 * 2 ^ 59
def prefixEnd_4651116 : Nat := 4983230072969 + 3 ^ 40 * 4651116 * 2
def baseEnd_4651116 : Nat := 265362009757481080106657

theorem tailTrace_4651116 : CollatzResearch.WordTrace tailWord_4651116 prefixEnd_4651116 265362009757481080106657 := by
  unfold tailWord_4651116
  simp only [CollatzResearch.WordTrace]
  refine ⟨84820068508904277108342601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113093424678539036144456801 84820068508904277108342601)
  ·
    refine ⟨63615051381678207831256951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84820068508904277108342601 63615051381678207831256951)
    ·
      refine ⟨95422577072517311746885427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63615051381678207831256951 95422577072517311746885427)
      ·
        refine ⟨143133865608775967620328141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95422577072517311746885427 143133865608775967620328141)
        ·
          refine ⟨53675199603290987857623053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 143133865608775967620328141 53675199603290987857623053)
          ·
            refine ⟨20128199851234120446608645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53675199603290987857623053 20128199851234120446608645)
            ·
              refine ⟨3774037472106397583739121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20128199851234120446608645 3774037472106397583739121)
              ·
                refine ⟨2830528104079798187804341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3774037472106397583739121 2830528104079798187804341)
                ·
                  refine ⟨265362009757481080106657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2830528104079798187804341 265362009757481080106657)
                  ·
                    rfl

theorem cell23_4651116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 4, 2, 5].length) (baseStart_4651116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4651116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4651116 prefixEnd_4651116 := by exact prefixLift 4651116
  have htrace : WordTrace (prefixWord ++ tailWord_4651116) baseStart_4651116 baseEnd_4651116 := by
    simpa [prefixWord, tailWord_4651116, baseEnd_4651116] using wordTrace_append hprefix tailTrace_4651116
  have hstable : (prefixWord ++ tailWord_4651116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4651116).length < 2 ^ (prefixWord ++ tailWord_4651116).sum := by decide
  have hdescent : baseEnd_4651116 < baseStart_4651116 := by decide
  rcases family_descends (prefixWord ++ tailWord_4651116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4651119 : List Nat := [1, 1, 2, 1, 3, 4, 1, 1, 2, 5, 2]
def baseStart_4651119 : Nat := 118140960795 + 4651119 * 2 ^ 59
def prefixEnd_4651119 : Nat := 4983230072969 + 3 ^ 40 * 4651119 * 2
def baseEnd_4651119 : Nat := 2388259628259293209222399

theorem tailTrace_4651119 : CollatzResearch.WordTrace tailWord_4651119 prefixEnd_4651119 2388259628259293209222399 := by
  unfold tailWord_4651119
  simp only [CollatzResearch.WordTrace]
  refine ⟨169640246436797685729044411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113093497624531790486029607 169640246436797685729044411)
  ·
    refine ⟨254460369655196528593566617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169640246436797685729044411 254460369655196528593566617)
    ·
      refine ⟨190845277241397396445174963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 254460369655196528593566617 190845277241397396445174963)
      ·
        refine ⟨286267915862096094667762445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190845277241397396445174963 286267915862096094667762445)
        ·
          refine ⟨107350468448286035500410917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 286267915862096094667762445 107350468448286035500410917)
          ·
            refine ⟨20128212834053631656327047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 107350468448286035500410917 20128212834053631656327047)
            ·
              refine ⟨30192319251080447484490571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20128212834053631656327047 30192319251080447484490571)
              ·
                refine ⟨45288478876620671226735857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30192319251080447484490571 45288478876620671226735857)
                ·
                  refine ⟨33966359157465503420051893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45288478876620671226735857 33966359157465503420051893)
                  ·
                    refine ⟨3184346171012390945629865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33966359157465503420051893 3184346171012390945629865)
                    ·
                      refine ⟨2388259628259293209222399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3184346171012390945629865 2388259628259293209222399)
                      ·
                        rfl

theorem cell23_4651119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 5, 2].length) (baseStart_4651119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4651119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4651119 prefixEnd_4651119 := by exact prefixLift 4651119
  have htrace : WordTrace (prefixWord ++ tailWord_4651119) baseStart_4651119 baseEnd_4651119 := by
    simpa [prefixWord, tailWord_4651119, baseEnd_4651119] using wordTrace_append hprefix tailTrace_4651119
  have hstable : (prefixWord ++ tailWord_4651119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4651119).length < 2 ^ (prefixWord ++ tailWord_4651119).sum := by decide
  have hdescent : baseEnd_4651119 < baseStart_4651119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4651119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4651126 : List Nat := [5, 1, 1, 2, 1, 3, 1, 1, 2, 3, 3]
def baseStart_4651126 : Nat := 118140960795 + 4651126 * 2 ^ 59
def prefixEnd_4651126 : Nat := 4983230072969 + 3 ^ 40 * 4651126 * 2
def baseEnd_4651126 : Nat := 2388263222623874681834867

theorem tailTrace_4651126 : CollatzResearch.WordTrace tailWord_4651126 prefixEnd_4651126 2388263222623874681834867 := by
  unfold tailWord_4651126
  simp only [CollatzResearch.WordTrace]
  refine ⟨10602531359235770370284327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 113093667831848217283032821 10602531359235770370284327)
  ·
    refine ⟨15903797038853655555426491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10602531359235770370284327 15903797038853655555426491)
    ·
      refine ⟨23855695558280483333139737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15903797038853655555426491 23855695558280483333139737)
      ·
        refine ⟨17891771668710362499854803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23855695558280483333139737 17891771668710362499854803)
        ·
          refine ⟨26837657503065543749782205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17891771668710362499854803 26837657503065543749782205)
          ·
            refine ⟨10064121563649578906168327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26837657503065543749782205 10064121563649578906168327)
            ·
              refine ⟨15096182345474368359252491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10064121563649578906168327 15096182345474368359252491)
              ·
                refine ⟨22644273518211552538878737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15096182345474368359252491 22644273518211552538878737)
                ·
                  refine ⟨16983205138658664404159053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22644273518211552538878737 16983205138658664404159053)
                  ·
                    refine ⟨6368701926996999151559645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16983205138658664404159053 6368701926996999151559645)
                    ·
                      refine ⟨2388263222623874681834867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6368701926996999151559645 2388263222623874681834867)
                      ·
                        rfl

theorem cell23_4651126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_4651126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4651126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4651126 prefixEnd_4651126 := by exact prefixLift 4651126
  have htrace : WordTrace (prefixWord ++ tailWord_4651126) baseStart_4651126 baseEnd_4651126 := by
    simpa [prefixWord, tailWord_4651126, baseEnd_4651126] using wordTrace_append hprefix tailTrace_4651126
  have hstable : (prefixWord ++ tailWord_4651126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4651126).length < 2 ^ (prefixWord ++ tailWord_4651126).sum := by decide
  have hdescent : baseEnd_4651126 < baseStart_4651126 := by decide
  rcases family_descends (prefixWord ++ tailWord_4651126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4651146 : List Nat := [3, 1, 2, 3, 1, 4, 1, 1, 2, 5]
def baseStart_4651146 : Nat := 118140960795 + 4651146 * 2 ^ 59
def prefixEnd_4651146 : Nat := 4983230072969 + 3 ^ 40 * 4651146 * 2
def baseEnd_4651146 : Nat := 796091164078988201194925

theorem tailTrace_4651146 : CollatzResearch.WordTrace tailWord_4651146 prefixEnd_4651146 796091164078988201194925 := by
  unfold tailWord_4651146
  simp only [CollatzResearch.WordTrace]
  refine ⟨42410307801924967335069323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113094154138466579560184861 42410307801924967335069323)
  ·
    refine ⟨63615461702887451002603985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42410307801924967335069323 63615461702887451002603985)
    ·
      refine ⟨47711596277165588251952989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63615461702887451002603985 47711596277165588251952989)
      ·
        refine ⟨17891848603937095594482371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47711596277165588251952989 17891848603937095594482371)
        ·
          refine ⟨26837772905905643391723557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17891848603937095594482371 26837772905905643391723557)
          ·
            refine ⟨5032082419857308135948167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26837772905905643391723557 5032082419857308135948167)
            ·
              refine ⟨7548123629785962203922251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5032082419857308135948167 7548123629785962203922251)
              ·
                refine ⟨11322185444678943305883377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7548123629785962203922251 11322185444678943305883377)
                ·
                  refine ⟨8491639083509207479412533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11322185444678943305883377 8491639083509207479412533)
                  ·
                    refine ⟨796091164078988201194925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8491639083509207479412533 796091164078988201194925)
                    ·
                      rfl

theorem cell23_4651146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 1, 2, 5].length) (baseStart_4651146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4651146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4651146 prefixEnd_4651146 := by exact prefixLift 4651146
  have htrace : WordTrace (prefixWord ++ tailWord_4651146) baseStart_4651146 baseEnd_4651146 := by
    simpa [prefixWord, tailWord_4651146, baseEnd_4651146] using wordTrace_append hprefix tailTrace_4651146
  have hstable : (prefixWord ++ tailWord_4651146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4651146).length < 2 ^ (prefixWord ++ tailWord_4651146).sum := by decide
  have hdescent : baseEnd_4651146 < baseStart_4651146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4651146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4651192 : List Nat := [2, 1, 2, 1, 2, 1, 3, 2, 1, 2, 6]
def baseStart_4651192 : Nat := 118140960795 + 4651192 * 2 ^ 59
def prefixEnd_4651192 : Nat := 4983230072969 + 3 ^ 40 * 4651192 * 2
def baseEnd_4651192 : Nat := 2388297112347071423609563

theorem tailTrace_4651192 : CollatzResearch.WordTrace tailWord_4651192 prefixEnd_4651192 2388297112347071423609563 := by
  unfold tailWord_4651192
  simp only [CollatzResearch.WordTrace]
  refine ⟨84821454482766609598225915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113095272643688812797634553 84821454482766609598225915)
  ·
    refine ⟨127232181724149914397338873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84821454482766609598225915 127232181724149914397338873)
    ·
      refine ⟨95424136293112435798004155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127232181724149914397338873 95424136293112435798004155)
      ·
        refine ⟨143136204439668653697006233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95424136293112435798004155 143136204439668653697006233)
        ·
          refine ⟨107352153329751490272754675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143136204439668653697006233 107352153329751490272754675)
          ·
            refine ⟨161028229994627235409132013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107352153329751490272754675 161028229994627235409132013)
            ·
              refine ⟨60385586247985213278424505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 161028229994627235409132013 60385586247985213278424505)
              ·
                refine ⟨45289189685988909958818379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60385586247985213278424505 45289189685988909958818379)
                ·
                  refine ⟨67933784528983364938227569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45289189685988909958818379 67933784528983364938227569)
                  ·
                    refine ⟨50950338396737523703670677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 67933784528983364938227569 50950338396737523703670677)
                    ·
                      refine ⟨2388297112347071423609563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50950338396737523703670677 2388297112347071423609563)
                      ·
                        rfl

theorem cell23_4651192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 1, 2, 6].length) (baseStart_4651192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4651192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4651192 prefixEnd_4651192 := by exact prefixLift 4651192
  have htrace : WordTrace (prefixWord ++ tailWord_4651192) baseStart_4651192 baseEnd_4651192 := by
    simpa [prefixWord, tailWord_4651192, baseEnd_4651192] using wordTrace_append hprefix tailTrace_4651192
  have hstable : (prefixWord ++ tailWord_4651192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4651192).length < 2 ^ (prefixWord ++ tailWord_4651192).sum := by decide
  have hdescent : baseEnd_4651192 < baseStart_4651192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4651192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4651226 : List Nat := [3, 1, 1, 2, 2, 1, 3, 1, 4, 3, 2]
def baseStart_4651226 : Nat := 118140960795 + 4651226 * 2 ^ 59
def prefixEnd_4651226 : Nat := 4983230072969 + 3 ^ 40 * 4651226 * 2
def baseEnd_4651226 : Nat := 2388314570689324290584407

theorem tailTrace_4651226 : CollatzResearch.WordTrace tailWord_4651226 prefixEnd_4651226 2388314570689324290584407 := by
  unfold tailWord_4651226
  simp only [CollatzResearch.WordTrace]
  refine ⟨42411037261852510750797383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113096099364940028668793021 42411037261852510750797383)
  ·
    refine ⟨63616555892778766126196075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42411037261852510750797383 63616555892778766126196075)
    ·
      refine ⟨95424833839168149189294113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63616555892778766126196075 95424833839168149189294113)
      ·
        refine ⟨71568625379376111891970585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95424833839168149189294113 71568625379376111891970585)
        ·
          refine ⟨53676469034532083918977939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71568625379376111891970585 53676469034532083918977939)
          ·
            refine ⟨80514703551798125878466909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53676469034532083918977939 80514703551798125878466909)
            ·
              refine ⟨30193013831924297204425091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80514703551798125878466909 30193013831924297204425091)
              ·
                refine ⟨45289520747886445806637637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30193013831924297204425091 45289520747886445806637637)
                ·
                  refine ⟨8491785140228708588744557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45289520747886445806637637 8491785140228708588744557)
                  ·
                    refine ⟨3184419427585765720779209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8491785140228708588744557 3184419427585765720779209)
                    ·
                      refine ⟨2388314570689324290584407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3184419427585765720779209 2388314570689324290584407)
                      ·
                        rfl

theorem cell23_4651226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 4, 3, 2].length) (baseStart_4651226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4651226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4651226 prefixEnd_4651226 := by exact prefixLift 4651226
  have htrace : WordTrace (prefixWord ++ tailWord_4651226) baseStart_4651226 baseEnd_4651226 := by
    simpa [prefixWord, tailWord_4651226, baseEnd_4651226] using wordTrace_append hprefix tailTrace_4651226
  have hstable : (prefixWord ++ tailWord_4651226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4651226).length < 2 ^ (prefixWord ++ tailWord_4651226).sum := by decide
  have hdescent : baseEnd_4651226 < baseStart_4651226 := by decide
  rcases family_descends (prefixWord ++ tailWord_4651226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4651266 : List Nat := [3, 4, 1, 1, 2, 1, 1, 1, 3, 6]
def baseStart_4651266 : Nat := 118140960795 + 4651266 * 2 ^ 59
def prefixEnd_4651266 : Nat := 4983230072969 + 3 ^ 40 * 4651266 * 2
def baseEnd_4651266 : Nat := 796111703305168044694741

theorem tailTrace_4651266 : CollatzResearch.WordTrace tailWord_4651266 prefixEnd_4651266 796111703305168044694741 := by
  unfold tailWord_4651266
  simp only [CollatzResearch.WordTrace]
  refine ⟨42411401991816282458661413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113097071978176753223097101 42411401991816282458661413)
  ·
    refine ⟨7952137873465552960999015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42411401991816282458661413 7952137873465552960999015)
    ·
      refine ⟨11928206810198329441498523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7952137873465552960999015 11928206810198329441498523)
      ·
        refine ⟨17892310215297494162247785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11928206810198329441498523 17892310215297494162247785)
        ·
          refine ⟨13419232661473120621685839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17892310215297494162247785 13419232661473120621685839)
          ·
            refine ⟨20128848992209680932528759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13419232661473120621685839 20128848992209680932528759)
            ·
              refine ⟨30193273488314521398793139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20128848992209680932528759 30193273488314521398793139)
              ·
                refine ⟨45289910232471782098189709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30193273488314521398793139 45289910232471782098189709)
                ·
                  refine ⟨16983716337176918286821141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45289910232471782098189709 16983716337176918286821141)
                  ·
                    refine ⟨796111703305168044694741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16983716337176918286821141 796111703305168044694741)
                    ·
                      rfl

theorem cell23_4651266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_4651266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4651266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4651266 prefixEnd_4651266 := by exact prefixLift 4651266
  have htrace : WordTrace (prefixWord ++ tailWord_4651266) baseStart_4651266 baseEnd_4651266 := by
    simpa [prefixWord, tailWord_4651266, baseEnd_4651266] using wordTrace_append hprefix tailTrace_4651266
  have hstable : (prefixWord ++ tailWord_4651266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4651266).length < 2 ^ (prefixWord ++ tailWord_4651266).sum := by decide
  have hdescent : baseEnd_4651266 < baseStart_4651266 := by decide
  rcases family_descends (prefixWord ++ tailWord_4651266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4651273 : List Nat := [1, 2, 1, 1, 3, 5, 3, 1, 1, 1, 4]
def baseStart_4651273 : Nat := 118140960795 + 4651273 * 2 ^ 59
def prefixEnd_4651273 : Nat := 4983230072969 + 3 ^ 40 * 4651273 * 2
def baseEnd_4651273 : Nat := 2388338704280085606696691

theorem tailTrace_4651273 : CollatzResearch.WordTrace tailWord_4651273 prefixEnd_4651273 2388338704280085606696691 := by
  unfold tailWord_4651273
  simp only [CollatzResearch.WordTrace]
  refine ⟨169645863278239770030150473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113097242185493180020100315 169645863278239770030150473)
  ·
    refine ⟨127234397458679827522612855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169645863278239770030150473 127234397458679827522612855)
    ·
      refine ⟨190851596188019741283919283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127234397458679827522612855 190851596188019741283919283)
      ·
        refine ⟨286277394282029611925878925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190851596188019741283919283 286277394282029611925878925)
        ·
          refine ⟨107354022855761104472204597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 286277394282029611925878925 107354022855761104472204597)
          ·
            refine ⟨10064439642727603544269181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 107354022855761104472204597 10064439642727603544269181)
            ·
              refine ⟨3774164866022851329100943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10064439642727603544269181 3774164866022851329100943)
              ·
                refine ⟨5661247299034276993651415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3774164866022851329100943 5661247299034276993651415)
                ·
                  refine ⟨8491870948551415490477123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5661247299034276993651415 8491870948551415490477123)
                  ·
                    refine ⟨12737806422827123235715685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8491870948551415490477123 12737806422827123235715685)
                    ·
                      refine ⟨2388338704280085606696691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12737806422827123235715685 2388338704280085606696691)
                      ·
                        rfl

theorem cell23_4651273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 3, 1, 1, 1, 4].length) (baseStart_4651273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4651273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4651273 prefixEnd_4651273 := by exact prefixLift 4651273
  have htrace : WordTrace (prefixWord ++ tailWord_4651273) baseStart_4651273 baseEnd_4651273 := by
    simpa [prefixWord, tailWord_4651273, baseEnd_4651273] using wordTrace_append hprefix tailTrace_4651273
  have hstable : (prefixWord ++ tailWord_4651273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4651273).length < 2 ^ (prefixWord ++ tailWord_4651273).sum := by decide
  have hdescent : baseEnd_4651273 < baseStart_4651273 := by decide
  rcases family_descends (prefixWord ++ tailWord_4651273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4651296 : List Nat := [2, 1, 1, 5, 2, 3, 1, 8]
def baseStart_4651296 : Nat := 118140960795 + 4651296 * 2 ^ 59
def prefixEnd_4651296 : Nat := 4983230072969 + 3 ^ 40 * 4651296 * 2
def baseEnd_4651296 : Nat := 88457426456857000618855

theorem tailTrace_4651296 : CollatzResearch.WordTrace tailWord_4651296 prefixEnd_4651296 88457426456857000618855 := by
  unfold tailWord_4651296
  simp only [CollatzResearch.WordTrace]
  refine ⟨84823351078578222479118871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113097801438104296638825161 84823351078578222479118871)
  ·
    refine ⟨127235026617867333718678307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84823351078578222479118871 127235026617867333718678307)
    ·
      refine ⟨190852539926801000578017461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127235026617867333718678307 190852539926801000578017461)
      ·
        refine ⟨17892425618137593804189137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 190852539926801000578017461 17892425618137593804189137)
        ·
          refine ⟨13419319213603195353141853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17892425618137593804189137 13419319213603195353141853)
          ·
            refine ⟨5032244705101198257428195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13419319213603195353141853 5032244705101198257428195)
            ·
              refine ⟨7548367057651797386142293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5032244705101198257428195 7548367057651797386142293)
              ·
                refine ⟨88457426456857000618855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7548367057651797386142293 88457426456857000618855)
                ·
                  rfl

theorem cell23_4651296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 8].length) (baseStart_4651296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4651296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4651296 prefixEnd_4651296 := by exact prefixLift 4651296
  have htrace : WordTrace (prefixWord ++ tailWord_4651296) baseStart_4651296 baseEnd_4651296 := by
    simpa [prefixWord, tailWord_4651296, baseEnd_4651296] using wordTrace_append hprefix tailTrace_4651296
  have hstable : (prefixWord ++ tailWord_4651296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4651296).length < 2 ^ (prefixWord ++ tailWord_4651296).sum := by decide
  have hdescent : baseEnd_4651296 < baseStart_4651296 := by decide
  rcases family_descends (prefixWord ++ tailWord_4651296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4651369 : List Nat := [1, 2, 1, 1, 1, 3, 3, 4, 7]
def baseStart_4651369 : Nat := 118140960795 + 4651369 * 2 ^ 59
def prefixEnd_4651369 : Nat := 4983230072969 + 3 ^ 40 * 4651369 * 2
def baseEnd_4651369 : Nat := 265376444269213025677361

theorem tailTrace_4651369 : CollatzResearch.WordTrace tailWord_4651369 prefixEnd_4651369 265376444269213025677361 := by
  unfold tailWord_4651369
  simp only [CollatzResearch.WordTrace]
  refine ⟨169649364685891978425645161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113099576457261318950430107 169649364685891978425645161)
  ·
    refine ⟨127237023514418983819233871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169649364685891978425645161 127237023514418983819233871)
    ·
      refine ⟨190855535271628475728850807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127237023514418983819233871 190855535271628475728850807)
      ·
        refine ⟨286283302907442713593276211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190855535271628475728850807 286283302907442713593276211)
        ·
          refine ⟨429424954361164070389914317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 286283302907442713593276211 429424954361164070389914317)
          ·
            refine ⟨161034357885436526396217869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 429424954361164070389914317 161034357885436526396217869)
            ·
              refine ⟨60387884207038697398581701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 161034357885436526396217869 60387884207038697398581701)
              ·
                refine ⟨11322728288819755762234069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60387884207038697398581701 11322728288819755762234069)
                ·
                  refine ⟨265376444269213025677361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11322728288819755762234069 265376444269213025677361)
                  ·
                    rfl

theorem cell23_4651369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 4, 7].length) (baseStart_4651369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4651369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4651369 prefixEnd_4651369 := by exact prefixLift 4651369
  have htrace : WordTrace (prefixWord ++ tailWord_4651369) baseStart_4651369 baseEnd_4651369 := by
    simpa [prefixWord, tailWord_4651369, baseEnd_4651369] using wordTrace_append hprefix tailTrace_4651369
  have hstable : (prefixWord ++ tailWord_4651369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4651369).length < 2 ^ (prefixWord ++ tailWord_4651369).sum := by decide
  have hdescent : baseEnd_4651369 < baseStart_4651369 := by decide
  rcases family_descends (prefixWord ++ tailWord_4651369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4651426 : List Nat := [3, 3, 1, 2, 1, 1, 1, 2, 1, 1, 7]
def baseStart_4651426 : Nat := 118140960795 + 4651426 * 2 ^ 59
def prefixEnd_4651426 : Nat := 4983230072969 + 3 ^ 40 * 4651426 * 2
def baseEnd_4651426 : Nat := 2388417266820223508083487

theorem tailTrace_4651426 : CollatzResearch.WordTrace tailWord_4651426 prefixEnd_4651426 2388417266820223508083487 := by
  unfold tailWord_4651426
  simp only [CollatzResearch.WordTrace]
  refine ⟨42412860911671369290117533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113100962431123651440313421 42412860911671369290117533)
  ·
    refine ⟨15904822841876763483794075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42412860911671369290117533 15904822841876763483794075)
    ·
      refine ⟨23857234262815145225691113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15904822841876763483794075 23857234262815145225691113)
      ·
        refine ⟨17892925697111358919268335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23857234262815145225691113 17892925697111358919268335)
        ·
          refine ⟨26839388545667038378902503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17892925697111358919268335 26839388545667038378902503)
          ·
            refine ⟨40259082818500557568353755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26839388545667038378902503 40259082818500557568353755)
            ·
              refine ⟨60388624227750836352530633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40259082818500557568353755 60388624227750836352530633)
              ·
                refine ⟨45291468170813127264397975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60388624227750836352530633 45291468170813127264397975)
                ·
                  refine ⟨67937202256219690896596963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45291468170813127264397975 67937202256219690896596963)
                  ·
                    refine ⟨101905803384329536344895445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 67937202256219690896596963 101905803384329536344895445)
                    ·
                      refine ⟨2388417266820223508083487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 101905803384329536344895445 2388417266820223508083487)
                      ·
                        rfl

theorem cell23_4651426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_4651426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4651426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4651426 prefixEnd_4651426 := by exact prefixLift 4651426
  have htrace : WordTrace (prefixWord ++ tailWord_4651426) baseStart_4651426 baseEnd_4651426 := by
    simpa [prefixWord, tailWord_4651426, baseEnd_4651426] using wordTrace_append hprefix tailTrace_4651426
  have hstable : (prefixWord ++ tailWord_4651426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4651426).length < 2 ^ (prefixWord ++ tailWord_4651426).sum := by decide
  have hdescent : baseEnd_4651426 < baseStart_4651426 := by decide
  rcases family_descends (prefixWord ++ tailWord_4651426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4651439 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 9]
def baseStart_4651439 : Nat := 118140960795 + 4651439 * 2 ^ 59
def prefixEnd_4651439 : Nat := 4983230072969 + 3 ^ 40 * 4651439 * 2
def baseEnd_4651439 : Nat := 2388423942068731957220927

theorem tailTrace_4651439 : CollatzResearch.WordTrace tailWord_4651439 prefixEnd_4651439 2388423942068731957220927 := by
  unfold tailWord_4651439
  simp only [CollatzResearch.WordTrace]
  refine ⟨169651917795638380380693371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113101278530425586920462247 169651917795638380380693371)
  ·
    refine ⟨254477876693457570571040057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169651917795638380380693371 254477876693457570571040057)
    ·
      refine ⟨190858407520093177928280043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 254477876693457570571040057 190858407520093177928280043)
      ·
        refine ⟨286287611280139766892420065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190858407520093177928280043 286287611280139766892420065)
        ·
          refine ⟨214715708460104825169315049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 286287611280139766892420065 214715708460104825169315049)
          ·
            refine ⟨161036781345078618876986287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 214715708460104825169315049 161036781345078618876986287)
            ·
              refine ⟨241555172017617928315479431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161036781345078618876986287 241555172017617928315479431)
              ·
                refine ⟨362332758026426892473219147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 241555172017617928315479431 362332758026426892473219147)
                ·
                  refine ⟨543499137039640338709828721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 362332758026426892473219147 543499137039640338709828721)
                  ·
                    refine ⟨407624352779730254032371541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 543499137039640338709828721 407624352779730254032371541)
                    ·
                      refine ⟨2388423942068731957220927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 407624352779730254032371541 2388423942068731957220927)
                      ·
                        rfl

theorem cell23_4651439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 9].length) (baseStart_4651439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4651439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4651439 prefixEnd_4651439 := by exact prefixLift 4651439
  have htrace : WordTrace (prefixWord ++ tailWord_4651439) baseStart_4651439 baseEnd_4651439 := by
    simpa [prefixWord, tailWord_4651439, baseEnd_4651439] using wordTrace_append hprefix tailTrace_4651439
  have hstable : (prefixWord ++ tailWord_4651439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4651439).length < 2 ^ (prefixWord ++ tailWord_4651439).sum := by decide
  have hdescent : baseEnd_4651439 < baseStart_4651439 := by decide
  rcases family_descends (prefixWord ++ tailWord_4651439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4651453 : List Nat := [1, 4, 1, 2, 2, 2, 2, 2, 2, 1, 4]
def baseStart_4651453 : Nat := 118140960795 + 4651453 * 2 ^ 59
def prefixEnd_4651453 : Nat := 4983230072969 + 3 ^ 40 * 4651453 * 2
def baseEnd_4651453 : Nat := 2388431130797894902445863

theorem tailTrace_4651453 : CollatzResearch.WordTrace tailWord_4651453 prefixEnd_4651453 2388431130797894902445863 := by
  unfold tailWord_4651453
  simp only [CollatzResearch.WordTrace]
  refine ⟨169652428417587660771703013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113101618945058440514468675 169652428417587660771703013)
  ·
    refine ⟨31809830328297686394694315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 169652428417587660771703013 31809830328297686394694315)
    ·
      refine ⟨47714745492446529592041473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31809830328297686394694315 47714745492446529592041473)
      ·
        refine ⟨35786059119334897194031105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47714745492446529592041473 35786059119334897194031105)
        ·
          refine ⟨26839544339501172895523329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35786059119334897194031105 26839544339501172895523329)
          ·
            refine ⟨20129658254625879671642497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26839544339501172895523329 20129658254625879671642497)
            ·
              refine ⟨15097243690969409753731873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20129658254625879671642497 15097243690969409753731873)
              ·
                refine ⟨11322932768227057315298905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15097243690969409753731873 11322932768227057315298905)
                ·
                  refine ⟨8492199576170292986474179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11322932768227057315298905 8492199576170292986474179)
                  ·
                    refine ⟨12738299364255439479711269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8492199576170292986474179 12738299364255439479711269)
                    ·
                      refine ⟨2388431130797894902445863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12738299364255439479711269 2388431130797894902445863)
                      ·
                        rfl

theorem cell23_4651453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_4651453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4651453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4651453 prefixEnd_4651453 := by exact prefixLift 4651453
  have htrace : WordTrace (prefixWord ++ tailWord_4651453) baseStart_4651453 baseEnd_4651453 := by
    simpa [prefixWord, tailWord_4651453, baseEnd_4651453] using wordTrace_append hprefix tailTrace_4651453
  have hstable : (prefixWord ++ tailWord_4651453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4651453).length < 2 ^ (prefixWord ++ tailWord_4651453).sum := by decide
  have hdescent : baseEnd_4651453 < baseStart_4651453 := by decide
  rcases family_descends (prefixWord ++ tailWord_4651453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4651456 : List Nat := [2, 1, 1, 2, 3, 1, 1, 2, 3, 4, 3]
def baseStart_4651456 : Nat := 118140960795 + 4651456 * 2 ^ 59
def prefixEnd_4651456 : Nat := 4983230072969 + 3 ^ 40 * 4651456 * 2
def baseEnd_4651456 : Nat := 2388432671239858390708349

theorem tailTrace_4651456 : CollatzResearch.WordTrace tailWord_4651456 prefixEnd_4651456 2388432671239858390708349 := by
  unfold tailWord_4651456
  simp only [CollatzResearch.WordTrace]
  refine ⟨84826268918288396142031111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113101691891051194856041481 84826268918288396142031111)
  ·
    refine ⟨127239403377432594213046667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84826268918288396142031111 127239403377432594213046667)
    ·
      refine ⟨190859105066148891319570001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127239403377432594213046667 190859105066148891319570001)
      ·
        refine ⟨143144328799611668489677501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190859105066148891319570001 143144328799611668489677501)
        ·
          refine ⟨53679123299854375683629063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 143144328799611668489677501 53679123299854375683629063)
          ·
            refine ⟨80518684949781563525443595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53679123299854375683629063 80518684949781563525443595)
            ·
              refine ⟨120778027424672345288165393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80518684949781563525443595 120778027424672345288165393)
              ·
                refine ⟨90583520568504258966124045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 120778027424672345288165393 90583520568504258966124045)
                ·
                  refine ⟨33968820213189097112296517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 90583520568504258966124045 33968820213189097112296517)
                  ·
                    refine ⟨6369153789972955708555597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33968820213189097112296517 6369153789972955708555597)
                    ·
                      refine ⟨2388432671239858390708349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6369153789972955708555597 2388432671239858390708349)
                      ·
                        rfl

theorem cell23_4651456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 3, 4, 3].length) (baseStart_4651456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4651456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4651456 prefixEnd_4651456 := by exact prefixLift 4651456
  have htrace : WordTrace (prefixWord ++ tailWord_4651456) baseStart_4651456 baseEnd_4651456 := by
    simpa [prefixWord, tailWord_4651456, baseEnd_4651456] using wordTrace_append hprefix tailTrace_4651456
  have hstable : (prefixWord ++ tailWord_4651456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4651456).length < 2 ^ (prefixWord ++ tailWord_4651456).sum := by decide
  have hdescent : baseEnd_4651456 < baseStart_4651456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4651456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4651503 : List Nat := [1, 1, 2, 1, 4, 1, 1, 1, 7, 1, 3]
def baseStart_4651503 : Nat := 118140960795 + 4651503 * 2 ^ 59
def prefixEnd_4651503 : Nat := 4983230072969 + 3 ^ 40 * 4651503 * 2
def baseEnd_4651503 : Nat := 2388456804830619706820633

theorem tailTrace_4651503 : CollatzResearch.WordTrace tailWord_4651503 prefixEnd_4651503 2388456804830619706820633 := by
  unfold tailWord_4651503
  simp only [CollatzResearch.WordTrace]
  refine ⟨169654252067406519311023163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113102834711604346207348775 169654252067406519311023163)
  ·
    refine ⟨254481378101109778966534745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169654252067406519311023163 254481378101109778966534745)
    ·
      refine ⟨190861033575832334224901059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 254481378101109778966534745 190861033575832334224901059)
      ·
        refine ⟨286291550363748501337351589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190861033575832334224901059 286291550363748501337351589)
        ·
          refine ⟨53679665693202844000753423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 286291550363748501337351589 53679665693202844000753423)
          ·
            refine ⟨80519498539804266001130135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53679665693202844000753423 80519498539804266001130135)
            ·
              refine ⟨120779247809706399001695203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80519498539804266001130135 120779247809706399001695203)
              ·
                refine ⟨181168871714559598502542805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120779247809706399001695203 181168871714559598502542805)
                ·
                  refine ⟨4246145430809990589903347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 181168871714559598502542805 4246145430809990589903347)
                  ·
                    refine ⟨6369218146214985884855021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4246145430809990589903347 6369218146214985884855021)
                    ·
                      refine ⟨2388456804830619706820633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6369218146214985884855021 2388456804830619706820633)
                      ·
                        rfl

theorem cell23_4651503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 7, 1, 3].length) (baseStart_4651503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4651503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4651503 prefixEnd_4651503 := by exact prefixLift 4651503
  have htrace : WordTrace (prefixWord ++ tailWord_4651503) baseStart_4651503 baseEnd_4651503 := by
    simpa [prefixWord, tailWord_4651503, baseEnd_4651503] using wordTrace_append hprefix tailTrace_4651503
  have hstable : (prefixWord ++ tailWord_4651503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4651503).length < 2 ^ (prefixWord ++ tailWord_4651503).sum := by decide
  have hdescent : baseEnd_4651503 < baseStart_4651503 := by decide
  rcases family_descends (prefixWord ++ tailWord_4651503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4651553 : List Nat := [1, 2, 3, 2, 2, 1, 1, 1, 6, 4]
def baseStart_4651553 : Nat := 118140960795 + 4651553 * 2 ^ 59
def prefixEnd_4651553 : Nat := 4983230072969 + 3 ^ 40 * 4651553 * 2
def baseEnd_4651553 : Nat := 796160826287781503731801

theorem tailTrace_4651553 : CollatzResearch.WordTrace tailWord_4651553 prefixEnd_4651553 796160826287781503731801 := by
  unfold tailWord_4651553
  simp only [CollatzResearch.WordTrace]
  refine ⟨169656075717225377850343313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113104050478150251900228875 169656075717225377850343313)
  ·
    refine ⟨127242056787919033387757485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169656075717225377850343313 127242056787919033387757485)
    ·
      refine ⟨47715771295469637520409057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127242056787919033387757485 47715771295469637520409057)
      ·
        refine ⟨35786828471602228140306793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47715771295469637520409057 35786828471602228140306793)
        ·
          refine ⟨26840121353701671105230095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35786828471602228140306793 26840121353701671105230095)
          ·
            refine ⟨40260182030552506657845143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26840121353701671105230095 40260182030552506657845143)
            ·
              refine ⟨60390273045828759986767715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40260182030552506657845143 60390273045828759986767715)
              ·
                refine ⟨90585409568743139980151573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60390273045828759986767715 90585409568743139980151573)
                ·
                  refine ⟨4246191073534834686569605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 90585409568743139980151573 4246191073534834686569605)
                  ·
                    refine ⟨796160826287781503731801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4246191073534834686569605 796160826287781503731801)
                    ·
                      rfl

theorem cell23_4651553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 6, 4].length) (baseStart_4651553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4651553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4651553 prefixEnd_4651553 := by exact prefixLift 4651553
  have htrace : WordTrace (prefixWord ++ tailWord_4651553) baseStart_4651553 baseEnd_4651553 := by
    simpa [prefixWord, tailWord_4651553, baseEnd_4651553] using wordTrace_append hprefix tailTrace_4651553
  have hstable : (prefixWord ++ tailWord_4651553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4651553).length < 2 ^ (prefixWord ++ tailWord_4651553).sum := by decide
  have hdescent : baseEnd_4651553 < baseStart_4651553 := by decide
  rcases family_descends (prefixWord ++ tailWord_4651553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4651597 : List Nat := [1, 6, 1, 1, 2, 2, 1, 1, 3, 2, 3]
def baseStart_4651597 : Nat := 118140960795 + 4651597 * 2 ^ 59
def prefixEnd_4651597 : Nat := 4983230072969 + 3 ^ 40 * 4651597 * 2
def baseEnd_4651597 : Nat := 2388505072012142339045201

theorem tailTrace_4651597 : CollatzResearch.WordTrace tailWord_4651597 prefixEnd_4651597 2388505072012142339045201 := by
  unfold tailWord_4651597
  simp only [CollatzResearch.WordTrace]
  refine ⟨169657680529065973364945045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113105120352710648909963363 169657680529065973364945045)
  ·
    refine ⟨7952703774799967501481799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 169657680529065973364945045 7952703774799967501481799)
    ·
      refine ⟨11929055662199951252222699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7952703774799967501481799 11929055662199951252222699)
      ·
        refine ⟨17893583493299926878334049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11929055662199951252222699 17893583493299926878334049)
        ·
          refine ⟨13420187619974945158750537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17893583493299926878334049 13420187619974945158750537)
          ·
            refine ⟨10065140714981208869062903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13420187619974945158750537 10065140714981208869062903)
            ·
              refine ⟨15097711072471813303594355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10065140714981208869062903 15097711072471813303594355)
              ·
                refine ⟨22646566608707719955391533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15097711072471813303594355 22646566608707719955391533)
                ·
                  refine ⟨8492462478265394983271825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22646566608707719955391533 8492462478265394983271825)
                  ·
                    refine ⟨6369346858699046237453869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8492462478265394983271825 6369346858699046237453869)
                    ·
                      refine ⟨2388505072012142339045201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6369346858699046237453869 2388505072012142339045201)
                      ·
                        rfl

theorem cell23_4651597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_4651597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4651597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4651597 prefixEnd_4651597 := by exact prefixLift 4651597
  have htrace : WordTrace (prefixWord ++ tailWord_4651597) baseStart_4651597 baseEnd_4651597 := by
    simpa [prefixWord, tailWord_4651597, baseEnd_4651597] using wordTrace_append hprefix tailTrace_4651597
  have hstable : (prefixWord ++ tailWord_4651597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4651597).length < 2 ^ (prefixWord ++ tailWord_4651597).sum := by decide
  have hdescent : baseEnd_4651597 < baseStart_4651597 := by decide
  rcases family_descends (prefixWord ++ tailWord_4651597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4651724 : List Nat := [2, 2, 1, 5, 1, 3, 1, 3, 5]
def baseStart_4651724 : Nat := 118140960795 + 4651724 * 2 ^ 59
def prefixEnd_4651724 : Nat := 4983230072969 + 3 ^ 40 * 4651724 * 2
def baseEnd_4651724 : Nat := 265396698228362593573013

theorem tailTrace_4651724 : CollatzResearch.WordTrace tailWord_4651724 prefixEnd_4651724 265396698228362593573013 := by
  unfold tailWord_4651724
  simp only [CollatzResearch.WordTrace]
  refine ⟨84831156299802937027409113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113108208399737249369878817 84831156299802937027409113)
  ·
    refine ⟨63623367224852202770556835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84831156299802937027409113 63623367224852202770556835)
    ·
      refine ⟨95435050837278304155835253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63623367224852202770556835 95435050837278304155835253)
      ·
        refine ⟨8947036015994841014609555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 95435050837278304155835253 8947036015994841014609555)
        ·
          refine ⟨13420554023992261521914333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8947036015994841014609555 13420554023992261521914333)
          ·
            refine ⟨5032707758997098070717875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13420554023992261521914333 5032707758997098070717875)
            ·
              refine ⟨7549061638495647106076813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5032707758997098070717875 7549061638495647106076813)
              ·
                refine ⟨2830898114435867664778805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7549061638495647106076813 2830898114435867664778805)
                ·
                  refine ⟨265396698228362593573013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2830898114435867664778805 265396698228362593573013)
                  ·
                    rfl

theorem cell23_4651724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 3, 5].length) (baseStart_4651724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4651724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4651724 prefixEnd_4651724 := by exact prefixLift 4651724
  have htrace : WordTrace (prefixWord ++ tailWord_4651724) baseStart_4651724 baseEnd_4651724 := by
    simpa [prefixWord, tailWord_4651724, baseEnd_4651724] using wordTrace_append hprefix tailTrace_4651724
  have hstable : (prefixWord ++ tailWord_4651724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4651724).length < 2 ^ (prefixWord ++ tailWord_4651724).sum := by decide
  have hdescent : baseEnd_4651724 < baseStart_4651724 := by decide
  rcases family_descends (prefixWord ++ tailWord_4651724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4651753 : List Nat := [1, 2, 1, 1, 1, 2, 4, 2, 2, 1, 6]
def baseStart_4651753 : Nat := 118140960795 + 4651753 * 2 ^ 59
def prefixEnd_4651753 : Nat := 4983230072969 + 3 ^ 40 * 4651753 * 2
def baseEnd_4651753 : Nat := 2388585174994243728694483

theorem tailTrace_4651753 : CollatzResearch.WordTrace tailWord_4651753 prefixEnd_4651753 2388585174994243728694483 := by
  unfold tailWord_4651753
  simp only [CollatzResearch.WordTrace]
  refine ⟨169663370316500812007623913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113108913544333874671749275 169663370316500812007623913)
  ·
    refine ⟨127247527737375609005717935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169663370316500812007623913 127247527737375609005717935)
    ·
      refine ⟨190871291606063413508576903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127247527737375609005717935 190871291606063413508576903)
      ·
        refine ⟨286306937409095120262865355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190871291606063413508576903 286306937409095120262865355)
        ·
          refine ⟨429460406113642680394298033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 286306937409095120262865355 429460406113642680394298033)
          ·
            refine ⟨322095304585232010295723525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 429460406113642680394298033 322095304585232010295723525)
            ·
              refine ⟨60392869609731001930448161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 322095304585232010295723525 60392869609731001930448161)
              ·
                refine ⟨45294652207298251447836121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60392869609731001930448161 45294652207298251447836121)
                ·
                  refine ⟨33970989155473688585877091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45294652207298251447836121 33970989155473688585877091)
                  ·
                    refine ⟨50956483733210532878815637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33970989155473688585877091 50956483733210532878815637)
                    ·
                      refine ⟨2388585174994243728694483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50956483733210532878815637 2388585174994243728694483)
                      ·
                        rfl

theorem cell23_4651753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 1, 6].length) (baseStart_4651753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4651753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4651753 prefixEnd_4651753 := by exact prefixLift 4651753
  have htrace : WordTrace (prefixWord ++ tailWord_4651753) baseStart_4651753 baseEnd_4651753 := by
    simpa [prefixWord, tailWord_4651753, baseEnd_4651753] using wordTrace_append hprefix tailTrace_4651753
  have hstable : (prefixWord ++ tailWord_4651753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4651753).length < 2 ^ (prefixWord ++ tailWord_4651753).sum := by decide
  have hdescent : baseEnd_4651753 < baseStart_4651753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4651753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4651757 : List Nat := [1, 5, 1, 2, 1, 1, 2, 1, 1, 6, 2]
def baseStart_4651757 : Nat := 118140960795 + 4651757 * 2 ^ 59
def prefixEnd_4651757 : Nat := 4983230072969 + 3 ^ 40 * 4651757 * 2
def baseEnd_4651757 : Nat := 2388587228916861713044465

theorem tailTrace_4651757 : CollatzResearch.WordTrace tailWord_4651757 prefixEnd_4651757 2388587228916861713044465 := by
  unfold tailWord_4651757
  simp only [CollatzResearch.WordTrace]
  refine ⟨169663516208486320690769525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113109010805657547127179683 169663516208486320690769525)
  ·
    refine ⟨15905954644545592564759643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 169663516208486320690769525 15905954644545592564759643)
    ·
      refine ⟨23858931966818388847139465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15905954644545592564759643 23858931966818388847139465)
      ·
        refine ⟨17894198975113791635354599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23858931966818388847139465 17894198975113791635354599)
        ·
          refine ⟨26841298462670687453031899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17894198975113791635354599 26841298462670687453031899)
          ·
            refine ⟨40261947694006031179547849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26841298462670687453031899 40261947694006031179547849)
            ·
              refine ⟨30196460770504523384660887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40261947694006031179547849 30196460770504523384660887)
              ·
                refine ⟨45294691155756785076991331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30196460770504523384660887 45294691155756785076991331)
                ·
                  refine ⟨67942036733635177615486997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45294691155756785076991331 67942036733635177615486997)
                  ·
                    refine ⟨3184782971889148950725953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 67942036733635177615486997 3184782971889148950725953)
                    ·
                      refine ⟨2388587228916861713044465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3184782971889148950725953 2388587228916861713044465)
                      ·
                        rfl

theorem cell23_4651757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 6, 2].length) (baseStart_4651757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4651757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4651757 prefixEnd_4651757 := by exact prefixLift 4651757
  have htrace : WordTrace (prefixWord ++ tailWord_4651757) baseStart_4651757 baseEnd_4651757 := by
    simpa [prefixWord, tailWord_4651757, baseEnd_4651757] using wordTrace_append hprefix tailTrace_4651757
  have hstable : (prefixWord ++ tailWord_4651757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4651757).length < 2 ^ (prefixWord ++ tailWord_4651757).sum := by decide
  have hdescent : baseEnd_4651757 < baseStart_4651757 := by decide
  rcases family_descends (prefixWord ++ tailWord_4651757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4651760 : List Nat := [2, 1, 1, 1, 3, 1, 3, 2, 4, 2, 3]
def baseStart_4651760 : Nat := 118140960795 + 4651760 * 2 ^ 59
def prefixEnd_4651760 : Nat := 4983230072969 + 3 ^ 40 * 4651760 * 2
def baseEnd_4651760 : Nat := 2388588769358825201306951

theorem tailTrace_4651760 : CollatzResearch.WordTrace tailWord_4651760 prefixEnd_4651760 2388588769358825201306951 := by
  unfold tailWord_4651760
  simp only [CollatzResearch.WordTrace]
  refine ⟨84831812813737726101564367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113109083751650301468752489 84831812813737726101564367)
  ·
    refine ⟨127247719220606589152346551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84831812813737726101564367 127247719220606589152346551)
    ·
      refine ⟨190871578830909883728519827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127247719220606589152346551 190871578830909883728519827)
      ·
        refine ⟨286307368246364825592779741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190871578830909883728519827 286307368246364825592779741)
        ·
          refine ⟨107365263092386809597292403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 286307368246364825592779741 107365263092386809597292403)
          ·
            refine ⟨161047894638580214395938605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107365263092386809597292403 161047894638580214395938605)
            ·
              refine ⟨60392960489467580398476977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 161047894638580214395938605 60392960489467580398476977)
              ·
                refine ⟨45294720367100685298857733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60392960489467580398476977 45294720367100685298857733)
                ·
                  refine ⟨8492760068831378493535825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45294720367100685298857733 8492760068831378493535825)
                  ·
                    refine ⟨6369570051623533870151869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8492760068831378493535825 6369570051623533870151869)
                    ·
                      refine ⟨2388588769358825201306951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6369570051623533870151869 2388588769358825201306951)
                      ·
                        rfl

theorem cell23_4651760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 4, 2, 3].length) (baseStart_4651760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4651760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4651760 prefixEnd_4651760 := by exact prefixLift 4651760
  have htrace : WordTrace (prefixWord ++ tailWord_4651760) baseStart_4651760 baseEnd_4651760 := by
    simpa [prefixWord, tailWord_4651760, baseEnd_4651760] using wordTrace_append hprefix tailTrace_4651760
  have hstable : (prefixWord ++ tailWord_4651760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4651760).length < 2 ^ (prefixWord ++ tailWord_4651760).sum := by decide
  have hdescent : baseEnd_4651760 < baseStart_4651760 := by decide
  rcases family_descends (prefixWord ++ tailWord_4651760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4651774 : List Nat := [4, 2, 2, 1, 2, 2, 2, 1, 2, 1, 4]
def baseStart_4651774 : Nat := 118140960795 + 4651774 * 2 ^ 59
def prefixEnd_4651774 : Nat := 4983230072969 + 3 ^ 40 * 4651774 * 2
def baseEnd_4651774 : Nat := 2388595958087988146531887

theorem tailTrace_4651774 : CollatzResearch.WordTrace tailWord_4651774 prefixEnd_4651774 2388595958087988146531887 := by
  unfold tailWord_4651774
  simp only [CollatzResearch.WordTrace]
  refine ⟨21208017031178091574267297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113109424166283155062758917 21208017031178091574267297)
  ·
    refine ⟨15906012773383568680700473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21208017031178091574267297 15906012773383568680700473)
    ·
      refine ⟨11929509580037676510525355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15906012773383568680700473 11929509580037676510525355)
      ·
        refine ⟨17894264370056514765788033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11929509580037676510525355 17894264370056514765788033)
        ·
          refine ⟨13420698277542386074341025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17894264370056514765788033 13420698277542386074341025)
          ·
            refine ⟨10065523708156789555755769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13420698277542386074341025 10065523708156789555755769)
            ·
              refine ⟨7549142781117592166816827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10065523708156789555755769 7549142781117592166816827)
              ·
                refine ⟨11323714171676388250225241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7549142781117592166816827 11323714171676388250225241)
                ·
                  refine ⟨8492785628757291187668931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11323714171676388250225241 8492785628757291187668931)
                  ·
                    refine ⟨12739178443135936781503397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8492785628757291187668931 12739178443135936781503397)
                    ·
                      refine ⟨2388595958087988146531887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12739178443135936781503397 2388595958087988146531887)
                      ·
                        rfl

theorem cell23_4651774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_4651774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4651774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4651774 prefixEnd_4651774 := by exact prefixLift 4651774
  have htrace : WordTrace (prefixWord ++ tailWord_4651774) baseStart_4651774 baseEnd_4651774 := by
    simpa [prefixWord, tailWord_4651774, baseEnd_4651774] using wordTrace_append hprefix tailTrace_4651774
  have hstable : (prefixWord ++ tailWord_4651774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4651774).length < 2 ^ (prefixWord ++ tailWord_4651774).sum := by decide
  have hdescent : baseEnd_4651774 < baseStart_4651774 := by decide
  rcases family_descends (prefixWord ++ tailWord_4651774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4651803 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 7]
def baseStart_4651803 : Nat := 118140960795 + 4651803 * 2 ^ 59
def prefixEnd_4651803 : Nat := 4983230072969 + 3 ^ 40 * 4651803 * 2
def baseEnd_4651803 : Nat := 2388610849026968533069253

theorem tailTrace_4651803 : CollatzResearch.WordTrace tailWord_4651803 prefixEnd_4651803 2388610849026968533069253 := by
  unfold tailWord_4651803
  simp only [CollatzResearch.WordTrace]
  refine ⟨169665193966319670546944063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113110129310879780364629375 169665193966319670546944063)
  ·
    refine ⟨254497790949479505820416095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169665193966319670546944063 254497790949479505820416095)
    ·
      refine ⟨381746686424219258730624143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254497790949479505820416095 381746686424219258730624143)
      ·
        refine ⟨572620029636328888095936215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 381746686424219258730624143 572620029636328888095936215)
        ·
          refine ⟨858930044454493332143904323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 572620029636328888095936215 858930044454493332143904323)
          ·
            refine ⟨1288395066681739998215856485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 858930044454493332143904323 1288395066681739998215856485)
            ·
              refine ⟨241574075002826249665473091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1288395066681739998215856485 241574075002826249665473091)
              ·
                refine ⟨362361112504239374498209637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 241574075002826249665473091 362361112504239374498209637)
                ·
                  refine ⟨67942708594544882718414307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 362361112504239374498209637 67942708594544882718414307)
                  ·
                    refine ⟨101914062891817324077621461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 67942708594544882718414307 101914062891817324077621461)
                    ·
                      refine ⟨2388610849026968533069253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 101914062891817324077621461 2388610849026968533069253)
                      ·
                        rfl

theorem cell23_4651803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 7].length) (baseStart_4651803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4651803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4651803 prefixEnd_4651803 := by exact prefixLift 4651803
  have htrace : WordTrace (prefixWord ++ tailWord_4651803) baseStart_4651803 baseEnd_4651803 := by
    simpa [prefixWord, tailWord_4651803, baseEnd_4651803] using wordTrace_append hprefix tailTrace_4651803
  have hstable : (prefixWord ++ tailWord_4651803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4651803).length < 2 ^ (prefixWord ++ tailWord_4651803).sum := by decide
  have hdescent : baseEnd_4651803 < baseStart_4651803 := by decide
  rcases family_descends (prefixWord ++ tailWord_4651803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4651828 : List Nat := [2, 5, 1, 1, 4, 1, 1, 1, 2, 2, 3]
def baseStart_4651828 : Nat := 118140960795 + 4651828 * 2 ^ 59
def prefixEnd_4651828 : Nat := 4983230072969 + 3 ^ 40 * 4651828 * 2
def baseEnd_4651828 : Nat := 2388623686043330935256639

theorem tailTrace_4651828 : CollatzResearch.WordTrace tailWord_4651828 prefixEnd_4651828 2388623686043330935256639 := by
  unfold tailWord_4651828
  simp only [CollatzResearch.WordTrace]
  refine ⟨84833052895614549908302069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113110737194152733211069425 84833052895614549908302069)
  ·
    refine ⟨7953098708963864053903319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 84833052895614549908302069 7953098708963864053903319)
    ·
      refine ⟨11929648063445796080854979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7953098708963864053903319 11929648063445796080854979)
      ·
        refine ⟨17894472095168694121282469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11929648063445796080854979 17894472095168694121282469)
        ·
          refine ⟨3355213517844130147740463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17894472095168694121282469 3355213517844130147740463)
          ·
            refine ⟨5032820276766195221610695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3355213517844130147740463 5032820276766195221610695)
            ·
              refine ⟨7549230415149292832416043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5032820276766195221610695 7549230415149292832416043)
              ·
                refine ⟨11323845622723939248624065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7549230415149292832416043 11323845622723939248624065)
                ·
                  refine ⟨8492884217042954436468049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11323845622723939248624065 8492884217042954436468049)
                  ·
                    refine ⟨6369663162782215827351037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8492884217042954436468049 6369663162782215827351037)
                    ·
                      refine ⟨2388623686043330935256639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6369663162782215827351037 2388623686043330935256639)
                      ·
                        rfl

theorem cell23_4651828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 1, 2, 2, 3].length) (baseStart_4651828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4651828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4651828 prefixEnd_4651828 := by exact prefixLift 4651828
  have htrace : WordTrace (prefixWord ++ tailWord_4651828) baseStart_4651828 baseEnd_4651828 := by
    simpa [prefixWord, tailWord_4651828, baseEnd_4651828] using wordTrace_append hprefix tailTrace_4651828
  have hstable : (prefixWord ++ tailWord_4651828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4651828).length < 2 ^ (prefixWord ++ tailWord_4651828).sum := by decide
  have hdescent : baseEnd_4651828 < baseStart_4651828 := by decide
  rcases family_descends (prefixWord ++ tailWord_4651828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4651834 : List Nat := [3, 1, 1, 1, 6, 1, 1, 1, 1, 5, 2]
def baseStart_4651834 : Nat := 118140960795 + 4651834 * 2 ^ 59
def prefixEnd_4651834 : Nat := 4983230072969 + 3 ^ 40 * 4651834 * 2
def baseEnd_4651834 : Nat := 2388626766927257911781611

theorem tailTrace_4651834 : CollatzResearch.WordTrace tailWord_4651834 prefixEnd_4651834 2388626766927257911781611 := by
  unfold tailWord_4651834
  simp only [CollatzResearch.WordTrace]
  refine ⟨42416581157301840710330639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113110883086138241894215037 42416581157301840710330639)
  ·
    refine ⟨63624871735952761065495959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42416581157301840710330639 63624871735952761065495959)
    ·
      refine ⟨95437307603929141598243939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63624871735952761065495959 95437307603929141598243939)
      ·
        refine ⟨143155961405893712397365909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95437307603929141598243939 143155961405893712397365909)
        ·
          refine ⟨6710435690901267768626527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 143155961405893712397365909 6710435690901267768626527)
          ·
            refine ⟨10065653536351901652939791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6710435690901267768626527 10065653536351901652939791)
            ·
              refine ⟨15098480304527852479409687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10065653536351901652939791 15098480304527852479409687)
              ·
                refine ⟨22647720456791778719114531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15098480304527852479409687 22647720456791778719114531)
                ·
                  refine ⟨33971580685187668078671797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22647720456791778719114531 33971580685187668078671797)
                  ·
                    refine ⟨3184835689236343882375481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33971580685187668078671797 3184835689236343882375481)
                    ·
                      refine ⟨2388626766927257911781611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3184835689236343882375481 2388626766927257911781611)
                      ·
                        rfl

theorem cell23_4651834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 1, 5, 2].length) (baseStart_4651834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4651834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4651834 prefixEnd_4651834 := by exact prefixLift 4651834
  have htrace : WordTrace (prefixWord ++ tailWord_4651834) baseStart_4651834 baseEnd_4651834 := by
    simpa [prefixWord, tailWord_4651834, baseEnd_4651834] using wordTrace_append hprefix tailTrace_4651834
  have hstable : (prefixWord ++ tailWord_4651834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4651834).length < 2 ^ (prefixWord ++ tailWord_4651834).sum := by decide
  have hdescent : baseEnd_4651834 < baseStart_4651834 := by decide
  rcases family_descends (prefixWord ++ tailWord_4651834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4651877 : List Nat := [1, 3, 1, 3, 1, 1, 5, 1, 1, 2, 4]
def baseStart_4651877 : Nat := 118140960795 + 4651877 * 2 ^ 59
def prefixEnd_4651877 : Nat := 4983230072969 + 3 ^ 40 * 4651877 * 2
def baseEnd_4651877 : Nat := 2388648846595401243543913

theorem tailTrace_4651877 : CollatzResearch.WordTrace tailWord_4651877 prefixEnd_4651877 2388648846595401243543913 := by
  unfold tailWord_4651877
  simp only [CollatzResearch.WordTrace]
  refine ⟨169667892968051581185137885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113111928645367720790091923 169667892968051581185137885)
  ·
    refine ⟨63625459863019342944426707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169667892968051581185137885 63625459863019342944426707)
    ·
      refine ⟨95438189794529014416640061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63625459863019342944426707 95438189794529014416640061)
      ·
        refine ⟨35789321172948380406240023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95438189794529014416640061 35789321172948380406240023)
        ·
          refine ⟨53683981759422570609360035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35789321172948380406240023 53683981759422570609360035)
          ·
            refine ⟨80525972639133855914040053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53683981759422570609360035 80525972639133855914040053)
            ·
              refine ⟨7549309934918798991941255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 80525972639133855914040053 7549309934918798991941255)
              ·
                refine ⟨11323964902378198487911883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7549309934918798991941255 11323964902378198487911883)
                ·
                  refine ⟨16985947353567297731867825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11323964902378198487911883 16985947353567297731867825)
                  ·
                    refine ⟨12739460515175473298900869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16985947353567297731867825 12739460515175473298900869)
                    ·
                      refine ⟨2388648846595401243543913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12739460515175473298900869 2388648846595401243543913)
                      ·
                        rfl

theorem cell23_4651877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 1, 1, 2, 4].length) (baseStart_4651877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4651877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4651877 prefixEnd_4651877 := by exact prefixLift 4651877
  have htrace : WordTrace (prefixWord ++ tailWord_4651877) baseStart_4651877 baseEnd_4651877 := by
    simpa [prefixWord, tailWord_4651877, baseEnd_4651877] using wordTrace_append hprefix tailTrace_4651877
  have hstable : (prefixWord ++ tailWord_4651877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4651877).length < 2 ^ (prefixWord ++ tailWord_4651877).sum := by decide
  have hdescent : baseEnd_4651877 < baseStart_4651877 := by decide
  rcases family_descends (prefixWord ++ tailWord_4651877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4651884 : List Nat := [2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 3]
def baseStart_4651884 : Nat := 118140960795 + 4651884 * 2 ^ 59
def prefixEnd_4651884 : Nat := 4983230072969 + 3 ^ 40 * 4651884 * 2
def baseEnd_4651884 : Nat := 2388652440959982716156381

theorem tailTrace_4651884 : CollatzResearch.WordTrace tailWord_4651884 prefixEnd_4651884 2388652440959982716156381 := by
  unfold tailWord_4651884
  simp only [CollatzResearch.WordTrace]
  refine ⟨84834074139513110690321353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113112098852684147587095137 84834074139513110690321353)
  ·
    refine ⟨63625555604634833017741015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84834074139513110690321353 63625555604634833017741015)
    ·
      refine ⟨95438333406952249526611523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63625555604634833017741015 95438333406952249526611523)
      ·
        refine ⟨143157500110428374289917285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95438333406952249526611523 143157500110428374289917285)
        ·
          refine ⟨26842031270705320179359491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 143157500110428374289917285 26842031270705320179359491)
          ·
            refine ⟨40263046906057980269039237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26842031270705320179359491 40263046906057980269039237)
            ·
              refine ⟨7549321294885871300444857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40263046906057980269039237 7549321294885871300444857)
              ·
                refine ⟨5661990971164403475333643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7549321294885871300444857 5661990971164403475333643)
                ·
                  refine ⟨8492986456746605213000465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5661990971164403475333643 8492986456746605213000465)
                  ·
                    refine ⟨6369739842559953909750349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8492986456746605213000465 6369739842559953909750349)
                    ·
                      refine ⟨2388652440959982716156381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6369739842559953909750349 2388652440959982716156381)
                      ·
                        rfl

theorem cell23_4651884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 3].length) (baseStart_4651884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4651884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4651884 prefixEnd_4651884 := by exact prefixLift 4651884
  have htrace : WordTrace (prefixWord ++ tailWord_4651884) baseStart_4651884 baseEnd_4651884 := by
    simpa [prefixWord, tailWord_4651884, baseEnd_4651884] using wordTrace_append hprefix tailTrace_4651884
  have hstable : (prefixWord ++ tailWord_4651884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4651884).length < 2 ^ (prefixWord ++ tailWord_4651884).sum := by decide
  have hdescent : baseEnd_4651884 < baseStart_4651884 := by decide
  rcases family_descends (prefixWord ++ tailWord_4651884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4651957 : List Nat := [1, 3, 3, 2, 1, 1, 1, 3, 2, 1, 5]
def baseStart_4651957 : Nat := 118140960795 + 4651957 * 2 ^ 59
def prefixEnd_4651957 : Nat := 4983230072969 + 3 ^ 40 * 4651957 * 2
def baseEnd_4651957 : Nat := 2388689925047760930543545

theorem tailTrace_4651957 : CollatzResearch.WordTrace tailWord_4651957 prefixEnd_4651957 2388689925047760930543545 := by
  unfold tailWord_4651957
  simp only [CollatzResearch.WordTrace]
  refine ⟨169670810807761754848050125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113113873871841169898700083 169670810807761754848050125)
  ·
    refine ⟨63626554052910658068018797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169670810807761754848050125 63626554052910658068018797)
    ·
      refine ⟨23859957769841496775507049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63626554052910658068018797 23859957769841496775507049)
      ·
        refine ⟨17894968327381122581630287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23859957769841496775507049 17894968327381122581630287)
        ·
          refine ⟨26842452491071683872445431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17894968327381122581630287 26842452491071683872445431)
          ·
            refine ⟨40263678736607525808668147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26842452491071683872445431 40263678736607525808668147)
            ·
              refine ⟨60395518104911288713002221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40263678736607525808668147 60395518104911288713002221)
              ·
                refine ⟨22648319289341733267375833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60395518104911288713002221 22648319289341733267375833)
                ·
                  refine ⟨16986239467006299950531875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22648319289341733267375833 16986239467006299950531875)
                  ·
                    refine ⟨25479359200509449925797813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16986239467006299950531875 25479359200509449925797813)
                    ·
                      refine ⟨2388689925047760930543545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25479359200509449925797813 2388689925047760930543545)
                      ·
                        rfl

theorem cell23_4651957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_4651957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4651957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4651957 prefixEnd_4651957 := by exact prefixLift 4651957
  have htrace : WordTrace (prefixWord ++ tailWord_4651957) baseStart_4651957 baseEnd_4651957 := by
    simpa [prefixWord, tailWord_4651957, baseEnd_4651957] using wordTrace_append hprefix tailTrace_4651957
  have hstable : (prefixWord ++ tailWord_4651957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4651957).length < 2 ^ (prefixWord ++ tailWord_4651957).sum := by decide
  have hdescent : baseEnd_4651957 < baseStart_4651957 := by decide
  rcases family_descends (prefixWord ++ tailWord_4651957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4651988 : List Nat := [2, 4, 1, 2, 1, 2, 2, 3, 2, 2, 2]
def baseStart_4651988 : Nat := 118140960795 + 4651988 * 2 ^ 59
def prefixEnd_4651988 : Nat := 4983230072969 + 3 ^ 40 * 4651988 * 2
def baseEnd_4651988 : Nat := 2388705842948050309255903

theorem tailTrace_4651988 : CollatzResearch.WordTrace tailWord_4651988 prefixEnd_4651988 2388705842948050309255903 := by
  unfold tailWord_4651988
  simp only [CollatzResearch.WordTrace]
  refine ⟨84835970735324723571214309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113114627647099631428285745 84835970735324723571214309)
  ·
    refine ⟨15906744512873385669602683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84835970735324723571214309 15906744512873385669602683)
    ·
      refine ⟨23860116769310078504404025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15906744512873385669602683 23860116769310078504404025)
      ·
        refine ⟨17895087576982558878303019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23860116769310078504404025 17895087576982558878303019)
        ·
          refine ⟨26842631365473838317454529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17895087576982558878303019 26842631365473838317454529)
          ·
            refine ⟨20131973524105378738090897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26842631365473838317454529 20131973524105378738090897)
            ·
              refine ⟨15098980143079034053568173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20131973524105378738090897 15098980143079034053568173)
              ·
                refine ⟨5662117553654637770088065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15098980143079034053568173 5662117553654637770088065)
                ·
                  refine ⟨4246588165240978327566049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5662117553654637770088065 4246588165240978327566049)
                  ·
                    refine ⟨3184941123930733745674537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4246588165240978327566049 3184941123930733745674537)
                    ·
                      refine ⟨2388705842948050309255903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3184941123930733745674537 2388705842948050309255903)
                      ·
                        rfl

theorem cell23_4651988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 3, 2, 2, 2].length) (baseStart_4651988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4651988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4651988 prefixEnd_4651988 := by exact prefixLift 4651988
  have htrace : WordTrace (prefixWord ++ tailWord_4651988) baseStart_4651988 baseEnd_4651988 := by
    simpa [prefixWord, tailWord_4651988, baseEnd_4651988] using wordTrace_append hprefix tailTrace_4651988
  have hstable : (prefixWord ++ tailWord_4651988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4651988).length < 2 ^ (prefixWord ++ tailWord_4651988).sum := by decide
  have hdescent : baseEnd_4651988 < baseStart_4651988 := by decide
  rcases family_descends (prefixWord ++ tailWord_4651988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4652027 : List Nat := [1, 1, 1, 1, 1, 3, 3, 3, 4, 1, 4]
def baseStart_4652027 : Nat := 118140960795 + 4652027 * 2 ^ 59
def prefixEnd_4652027 : Nat := 4983230072969 + 3 ^ 40 * 4652027 * 2
def baseEnd_4652027 : Nat := 2388725868693575656668223

theorem tailTrace_4652027 : CollatzResearch.WordTrace tailWord_4652027 prefixEnd_4652027 2388725868693575656668223 := by
  unfold tailWord_4652027
  simp only [CollatzResearch.WordTrace]
  refine ⟨169673363917508156803098335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113115575945005437868732223 169673363917508156803098335)
  ·
    refine ⟨254510045876262235204647503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169673363917508156803098335 254510045876262235204647503)
    ·
      refine ⟨381765068814393352806971255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254510045876262235204647503 381765068814393352806971255)
      ·
        refine ⟨572647603221590029210456883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 381765068814393352806971255 572647603221590029210456883)
        ·
          refine ⟨858971404832385043815685325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 572647603221590029210456883 858971404832385043815685325)
          ·
            refine ⟨322114276812144391430881997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 858971404832385043815685325 322114276812144391430881997)
            ·
              refine ⟨120792853804554146786580749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 322114276812144391430881997 120792853804554146786580749)
              ·
                refine ⟨45297320176707805044967781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120792853804554146786580749 45297320176707805044967781)
                ·
                  refine ⟨8493247533132713445931459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45297320176707805044967781 8493247533132713445931459)
                  ·
                    refine ⟨12739871299699070168897189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8493247533132713445931459 12739871299699070168897189)
                    ·
                      refine ⟨2388725868693575656668223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12739871299699070168897189 2388725868693575656668223)
                      ·
                        rfl

theorem cell23_4652027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 4, 1, 4].length) (baseStart_4652027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4652027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4652027 prefixEnd_4652027 := by exact prefixLift 4652027
  have htrace : WordTrace (prefixWord ++ tailWord_4652027) baseStart_4652027 baseEnd_4652027 := by
    simpa [prefixWord, tailWord_4652027, baseEnd_4652027] using wordTrace_append hprefix tailTrace_4652027
  have hstable : (prefixWord ++ tailWord_4652027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4652027).length < 2 ^ (prefixWord ++ tailWord_4652027).sum := by decide
  have hdescent : baseEnd_4652027 < baseStart_4652027 := by decide
  rcases family_descends (prefixWord ++ tailWord_4652027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4652067 : List Nat := [1, 1, 1, 4, 3, 2, 1, 2, 8]
def baseStart_4652067 : Nat := 118140960795 + 4652067 * 2 ^ 59
def prefixEnd_4652067 : Nat := 4983230072969 + 3 ^ 40 * 4652067 * 2
def baseEnd_4652067 : Nat := 265416267546639500018671

theorem tailTrace_4652067 : CollatzResearch.WordTrace tailWord_4652067 prefixEnd_4652067 265416267546639500018671 := by
  unfold tailWord_4652067
  simp only [CollatzResearch.WordTrace]
  refine ⟨169674822837363243634554455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113116548558242162423036303 169674822837363243634554455)
  ·
    refine ⟨254512234256044865451831683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169674822837363243634554455 254512234256044865451831683)
    ·
      refine ⟨381768351384067298177747525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254512234256044865451831683 381768351384067298177747525)
      ·
        refine ⟨71581565884512618408327661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 381768351384067298177747525 71581565884512618408327661)
        ·
          refine ⟨26843087206692231903122873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71581565884512618408327661 26843087206692231903122873)
          ·
            refine ⟨20132315405019173927342155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26843087206692231903122873 20132315405019173927342155)
            ·
              refine ⟨30198473107528760891013233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20132315405019173927342155 30198473107528760891013233)
              ·
                refine ⟨22648854830646570668259925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30198473107528760891013233 22648854830646570668259925)
                ·
                  refine ⟨265416267546639500018671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22648854830646570668259925 265416267546639500018671)
                  ·
                    rfl

theorem cell23_4652067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 8].length) (baseStart_4652067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4652067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4652067 prefixEnd_4652067 := by exact prefixLift 4652067
  have htrace : WordTrace (prefixWord ++ tailWord_4652067) baseStart_4652067 baseEnd_4652067 := by
    simpa [prefixWord, tailWord_4652067, baseEnd_4652067] using wordTrace_append hprefix tailTrace_4652067
  have hstable : (prefixWord ++ tailWord_4652067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4652067).length < 2 ^ (prefixWord ++ tailWord_4652067).sum := by decide
  have hdescent : baseEnd_4652067 < baseStart_4652067 := by decide
  rcases family_descends (prefixWord ++ tailWord_4652067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4652128 : List Nat := [2, 1, 1, 3, 2, 2, 2, 5, 1, 1, 3]
def baseStart_4652128 : Nat := 118140960795 + 4652128 * 2 ^ 59
def prefixEnd_4652128 : Nat := 4983230072969 + 3 ^ 40 * 4652128 * 2
def baseEnd_4652128 : Nat := 2388777730239679761505259

theorem tailTrace_4652128 : CollatzResearch.WordTrace tailWord_4652128 prefixEnd_4652128 2388777730239679761505259 := by
  unfold tailWord_4652128
  simp only [CollatzResearch.WordTrace]
  refine ⟨84838523845071125526262519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113118031793428167368350025 84838523845071125526262519)
  ·
    refine ⟨127257785767606688289393779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84838523845071125526262519 127257785767606688289393779)
    ·
      refine ⟨190886678651410032434090669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127257785767606688289393779 190886678651410032434090669)
      ·
        refine ⟨71582504494278762162784001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 190886678651410032434090669 71582504494278762162784001)
        ·
          refine ⟨53686878370709071622088001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71582504494278762162784001 53686878370709071622088001)
          ·
            refine ⟨40265158778031803716566001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53686878370709071622088001 40265158778031803716566001)
            ·
              refine ⟨30198869083523852787424501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40265158778031803716566001 30198869083523852787424501)
              ·
                refine ⟨2831143976580361198821047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30198869083523852787424501 2831143976580361198821047)
                ·
                  refine ⟨4246715964870541798231571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2831143976580361198821047 4246715964870541798231571)
                  ·
                    refine ⟨6370073947305812697347357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4246715964870541798231571 6370073947305812697347357)
                    ·
                      refine ⟨2388777730239679761505259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6370073947305812697347357 2388777730239679761505259)
                      ·
                        rfl

theorem cell23_4652128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 5, 1, 1, 3].length) (baseStart_4652128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4652128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4652128 prefixEnd_4652128 := by exact prefixLift 4652128
  have htrace : WordTrace (prefixWord ++ tailWord_4652128) baseStart_4652128 baseEnd_4652128 := by
    simpa [prefixWord, tailWord_4652128, baseEnd_4652128] using wordTrace_append hprefix tailTrace_4652128
  have hstable : (prefixWord ++ tailWord_4652128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4652128).length < 2 ^ (prefixWord ++ tailWord_4652128).sum := by decide
  have hdescent : baseEnd_4652128 < baseStart_4652128 := by decide
  rcases family_descends (prefixWord ++ tailWord_4652128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4652138 : List Nat := [3, 1, 3, 2, 2, 1, 2, 2, 2, 3, 2]
def baseStart_4652138 : Nat := 118140960795 + 4652138 * 2 ^ 59
def prefixEnd_4652138 : Nat := 4983230072969 + 3 ^ 40 * 4652138 * 2
def baseEnd_4652138 : Nat := 2388782865046224722380213

theorem tailTrace_4652138 : CollatzResearch.WordTrace tailWord_4652138 prefixEnd_4652138 2388782865046224722380213 := by
  unfold tailWord_4652138
  simp only [CollatzResearch.WordTrace]
  refine ⟨42419353105026505690097267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113118274946737348506926045 42419353105026505690097267)
  ·
    refine ⟨63629029657539758535145901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42419353105026505690097267 63629029657539758535145901)
    ·
      refine ⟨23860886121577409450679713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63629029657539758535145901 23860886121577409450679713)
      ·
        refine ⟨17895664591183057088009785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23860886121577409450679713 17895664591183057088009785)
        ·
          refine ⟨13421748443387292816007339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17895664591183057088009785 13421748443387292816007339)
          ·
            refine ⟨20132622665080939224011009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13421748443387292816007339 20132622665080939224011009)
            ·
              refine ⟨15099466998810704418008257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20132622665080939224011009 15099466998810704418008257)
              ·
                refine ⟨11324600249108028313506193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15099466998810704418008257 11324600249108028313506193)
                ·
                  refine ⟨8493450186831021235129645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11324600249108028313506193 8493450186831021235129645)
                  ·
                    refine ⟨3185043820061632963173617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8493450186831021235129645 3185043820061632963173617)
                    ·
                      refine ⟨2388782865046224722380213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3185043820061632963173617 2388782865046224722380213)
                      ·
                        rfl

theorem cell23_4652138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 2, 2, 3, 2].length) (baseStart_4652138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4652138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4652138 prefixEnd_4652138 := by exact prefixLift 4652138
  have htrace : WordTrace (prefixWord ++ tailWord_4652138) baseStart_4652138 baseEnd_4652138 := by
    simpa [prefixWord, tailWord_4652138, baseEnd_4652138] using wordTrace_append hprefix tailTrace_4652138
  have hstable : (prefixWord ++ tailWord_4652138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4652138).length < 2 ^ (prefixWord ++ tailWord_4652138).sum := by decide
  have hdescent : baseEnd_4652138 < baseStart_4652138 := by decide
  rcases family_descends (prefixWord ++ tailWord_4652138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4652161 : List Nat := [1, 2, 4, 2, 2, 2, 2, 1, 1, 6]
def baseStart_4652161 : Nat := 118140960795 + 4652161 * 2 ^ 59
def prefixEnd_4652161 : Nat := 4983230072969 + 3 ^ 40 * 4652161 * 2
def baseEnd_4652161 : Nat := 796264891700426044130869

theorem tailTrace_4652161 : CollatzResearch.WordTrace tailWord_4652161 prefixEnd_4652161 796264891700426044130869 := by
  unfold tailWord_4652161
  simp only [CollatzResearch.WordTrace]
  refine ⟨169678251299022697688476337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113118834199348465125650891 169678251299022697688476337)
  ·
    refine ⟨127258688474267023266357253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169678251299022697688476337 127258688474267023266357253)
    ·
      refine ⟨23861004088925066862441985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127258688474267023266357253 23861004088925066862441985)
      ·
        refine ⟨17895753066693800146831489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23861004088925066862441985 17895753066693800146831489)
        ·
          refine ⟨13421814800020350110123617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17895753066693800146831489 13421814800020350110123617)
          ·
            refine ⟨10066361100015262582592713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13421814800020350110123617 10066361100015262582592713)
            ·
              refine ⟨7549770825011446936944535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10066361100015262582592713 7549770825011446936944535)
              ·
                refine ⟨11324656237517170405416803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7549770825011446936944535 11324656237517170405416803)
                ·
                  refine ⟨16986984356275755608125205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11324656237517170405416803 16986984356275755608125205)
                  ·
                    refine ⟨796264891700426044130869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16986984356275755608125205 796264891700426044130869)
                    ·
                      rfl

theorem cell23_4652161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 1, 1, 6].length) (baseStart_4652161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4652161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4652161 prefixEnd_4652161 := by exact prefixLift 4652161
  have htrace : WordTrace (prefixWord ++ tailWord_4652161) baseStart_4652161 baseEnd_4652161 := by
    simpa [prefixWord, tailWord_4652161, baseEnd_4652161] using wordTrace_append hprefix tailTrace_4652161
  have hstable : (prefixWord ++ tailWord_4652161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4652161).length < 2 ^ (prefixWord ++ tailWord_4652161).sum := by decide
  have hdescent : baseEnd_4652161 < baseStart_4652161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4652161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4652187 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 3, 9]
def baseStart_4652187 : Nat := 118140960795 + 4652187 * 2 ^ 59
def prefixEnd_4652187 : Nat := 4983230072969 + 3 ^ 40 * 4652187 * 2
def baseEnd_4652187 : Nat := 796269341866098343555829

theorem tailTrace_4652187 : CollatzResearch.WordTrace tailWord_4652187 prefixEnd_4652187 796269341866098343555829 := by
  unfold tailWord_4652187
  simp only [CollatzResearch.WordTrace]
  refine ⟨169679199596928504128922815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113119466397952336085948543 169679199596928504128922815)
  ·
    refine ⟨254518799395392756193384223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169679199596928504128922815 254518799395392756193384223)
    ·
      refine ⟨381778199093089134290076335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254518799395392756193384223 381778199093089134290076335)
      ·
        refine ⟨572667298639633701435114503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 381778199093089134290076335 572667298639633701435114503)
        ·
          refine ⟨859000947959450552152671755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 572667298639633701435114503 859000947959450552152671755)
          ·
            refine ⟨1288501421939175828229007633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 859000947959450552152671755 1288501421939175828229007633)
            ·
              refine ⟨966376066454381871171755725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1288501421939175828229007633 966376066454381871171755725)
              ·
                refine ⟨362391024920393201689408397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 966376066454381871171755725 362391024920393201689408397)
                ·
                  refine ⟨135896634345147450633528149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 362391024920393201689408397 135896634345147450633528149)
                  ·
                    refine ⟨796269341866098343555829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 135896634345147450633528149 796269341866098343555829)
                    ·
                      rfl

theorem cell23_4652187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 9].length) (baseStart_4652187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4652187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4652187 prefixEnd_4652187 := by exact prefixLift 4652187
  have htrace : WordTrace (prefixWord ++ tailWord_4652187) baseStart_4652187 baseEnd_4652187 := by
    simpa [prefixWord, tailWord_4652187, baseEnd_4652187] using wordTrace_append hprefix tailTrace_4652187
  have hstable : (prefixWord ++ tailWord_4652187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4652187).length < 2 ^ (prefixWord ++ tailWord_4652187).sum := by decide
  have hdescent : baseEnd_4652187 < baseStart_4652187 := by decide
  rcases family_descends (prefixWord ++ tailWord_4652187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4652188 : List Nat := [2, 2, 3, 2, 1, 3, 1, 3, 1, 2, 3]
def baseStart_4652188 : Nat := 118140960795 + 4652188 * 2 ^ 59
def prefixEnd_4652188 : Nat := 4983230072969 + 3 ^ 40 * 4652188 * 2
def baseEnd_4652188 : Nat := 2388808539078949526754983

theorem tailTrace_4652188 : CollatzResearch.WordTrace tailWord_4652188 prefixEnd_4652188 2388808539078949526754983 := by
  unfold tailWord_4652188
  simp only [CollatzResearch.WordTrace]
  refine ⟨84839618034962440649854609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113119490713283254199806145 84839618034962440649854609)
  ·
    refine ⟨63629713526221830487390957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84839618034962440649854609 63629713526221830487390957)
    ·
      refine ⟨23861142572333186432771609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63629713526221830487390957 23861142572333186432771609)
      ·
        refine ⟨17895856929249889824578707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23861142572333186432771609 17895856929249889824578707)
        ·
          refine ⟨26843785393874834736868061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17895856929249889824578707 26843785393874834736868061)
          ·
            refine ⟨10066419522703063026325523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26843785393874834736868061 10066419522703063026325523)
            ·
              refine ⟨15099629284054594539488285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10066419522703063026325523 15099629284054594539488285)
              ·
                refine ⟨5662360981520472952308107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15099629284054594539488285 5662360981520472952308107)
                ·
                  refine ⟨8493541472280709428462161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5662360981520472952308107 8493541472280709428462161)
                  ·
                    refine ⟨6370156104210532071346621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8493541472280709428462161 6370156104210532071346621)
                    ·
                      refine ⟨2388808539078949526754983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6370156104210532071346621 2388808539078949526754983)
                      ·
                        rfl

theorem cell23_4652188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_4652188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4652188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4652188 prefixEnd_4652188 := by exact prefixLift 4652188
  have htrace : WordTrace (prefixWord ++ tailWord_4652188) baseStart_4652188 baseEnd_4652188 := by
    simpa [prefixWord, tailWord_4652188, baseEnd_4652188] using wordTrace_append hprefix tailTrace_4652188
  have hstable : (prefixWord ++ tailWord_4652188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4652188).length < 2 ^ (prefixWord ++ tailWord_4652188).sum := by decide
  have hdescent : baseEnd_4652188 < baseStart_4652188 := by decide
  rcases family_descends (prefixWord ++ tailWord_4652188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4652202 : List Nat := [3, 1, 5, 1, 1, 2, 2, 1, 3, 2, 2]
def baseStart_4652202 : Nat := 118140960795 + 4652202 * 2 ^ 59
def prefixEnd_4652202 : Nat := 4983230072969 + 3 ^ 40 * 4652202 * 2
def baseEnd_4652202 : Nat := 2388815727808112471979919

theorem tailTrace_4652202 : CollatzResearch.WordTrace tailWord_4652202 prefixEnd_4652202 2388815727808112471979919 := by
  unfold tailWord_4652202
  simp only [CollatzResearch.WordTrace]
  refine ⟨42419936672968540422679715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113119831127916107793812573 42419936672968540422679715)
  ·
    refine ⟨63629905009452810634019573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42419936672968540422679715 63629905009452810634019573)
    ·
      refine ⟨5965303594636200996939335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63629905009452810634019573 5965303594636200996939335)
      ·
        refine ⟨8947955391954301495409003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5965303594636200996939335 8947955391954301495409003)
        ·
          refine ⟨13421933087931452243113505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8947955391954301495409003 13421933087931452243113505)
          ·
            refine ⟨10066449815948589182335129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13421933087931452243113505 10066449815948589182335129)
            ·
              refine ⟨7549837361961441886751347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10066449815948589182335129 7549837361961441886751347)
              ·
                refine ⟨11324756042942162830127021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7549837361961441886751347 11324756042942162830127021)
                ·
                  refine ⟨4246783516103311061297633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11324756042942162830127021 4246783516103311061297633)
                  ·
                    refine ⟨3185087637077483295973225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4246783516103311061297633 3185087637077483295973225)
                    ·
                      refine ⟨2388815727808112471979919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3185087637077483295973225 2388815727808112471979919)
                      ·
                        rfl

theorem cell23_4652202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_4652202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4652202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4652202 prefixEnd_4652202 := by exact prefixLift 4652202
  have htrace : WordTrace (prefixWord ++ tailWord_4652202) baseStart_4652202 baseEnd_4652202 := by
    simpa [prefixWord, tailWord_4652202, baseEnd_4652202] using wordTrace_append hprefix tailTrace_4652202
  have hstable : (prefixWord ++ tailWord_4652202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4652202).length < 2 ^ (prefixWord ++ tailWord_4652202).sum := by decide
  have hdescent : baseEnd_4652202 < baseStart_4652202 := by decide
  rcases family_descends (prefixWord ++ tailWord_4652202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4652211 : List Nat := [1, 1, 1, 2, 3, 2, 2, 1, 5, 3, 2]
def baseStart_4652211 : Nat := 118140960795 + 4652211 * 2 ^ 59
def prefixEnd_4652211 : Nat := 4983230072969 + 3 ^ 40 * 4652211 * 2
def baseEnd_4652211 : Nat := 2388820349134002936767377

theorem tailTrace_4652211 : CollatzResearch.WordTrace tailWord_4652211 prefixEnd_4652211 2388820349134002936767377 := by
  unfold tailWord_4652211
  simp only [CollatzResearch.WordTrace]
  refine ⟨169680074948841556227796487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113120049965894370818530991 169680074948841556227796487)
  ·
    refine ⟨254520112423262334341694731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169680074948841556227796487 254520112423262334341694731)
    ·
      refine ⟨381780168634893501512542097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254520112423262334341694731 381780168634893501512542097)
      ·
        refine ⟨286335126476170126134406573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 381780168634893501512542097 286335126476170126134406573)
        ·
          refine ⟨107375672428563797300402465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 286335126476170126134406573 107375672428563797300402465)
          ·
            refine ⟨80531754321422847975301849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107375672428563797300402465 80531754321422847975301849)
            ·
              refine ⟨60398815741067135981476387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80531754321422847975301849 60398815741067135981476387)
              ·
                refine ⟨90598223611600703972214581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60398815741067135981476387 90598223611600703972214581)
                ·
                  refine ⟨8493583463587565997395117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 90598223611600703972214581 8493583463587565997395117)
                  ·
                    refine ⟨3185093798845337249023169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8493583463587565997395117 3185093798845337249023169)
                    ·
                      refine ⟨2388820349134002936767377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3185093798845337249023169 2388820349134002936767377)
                      ·
                        rfl

theorem cell23_4652211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 5, 3, 2].length) (baseStart_4652211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4652211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4652211 prefixEnd_4652211 := by exact prefixLift 4652211
  have htrace : WordTrace (prefixWord ++ tailWord_4652211) baseStart_4652211 baseEnd_4652211 := by
    simpa [prefixWord, tailWord_4652211, baseEnd_4652211] using wordTrace_append hprefix tailTrace_4652211
  have hstable : (prefixWord ++ tailWord_4652211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4652211).length < 2 ^ (prefixWord ++ tailWord_4652211).sum := by decide
  have hdescent : baseEnd_4652211 < baseStart_4652211 := by decide
  rcases family_descends (prefixWord ++ tailWord_4652211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4652241 : List Nat := [1, 2, 2, 1, 2, 2, 1, 3, 3, 4, 2]
def baseStart_4652241 : Nat := 118140960795 + 4652241 * 2 ^ 59
def prefixEnd_4652241 : Nat := 4983230072969 + 3 ^ 40 * 4652241 * 2
def baseEnd_4652241 : Nat := 2388835753553637819392239

theorem tailTrace_4652241 : CollatzResearch.WordTrace tailWord_4652241 prefixEnd_4652241 2388835753553637819392239 := by
  unfold tailWord_4652241
  simp only [CollatzResearch.WordTrace]
  refine ⟨169681169138732871351388577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113120779425821914234259051 169681169138732871351388577)
  ·
    refine ⟨127260876854049653513541433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169681169138732871351388577 127260876854049653513541433)
    ·
      refine ⟨95445657640537240135156075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127260876854049653513541433 95445657640537240135156075)
      ·
        refine ⟨143168486460805860202734113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95445657640537240135156075 143168486460805860202734113)
        ·
          refine ⟨107376364845604395152050585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143168486460805860202734113 107376364845604395152050585)
          ·
            refine ⟨80532273634203296364037939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107376364845604395152050585 80532273634203296364037939)
            ·
              refine ⟨120798410451304944546056909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80532273634203296364037939 120798410451304944546056909)
              ·
                refine ⟨45299403919239354204771341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120798410451304944546056909 45299403919239354204771341)
                ·
                  refine ⟨16987276469714757826789253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45299403919239354204771341 16987276469714757826789253)
                  ·
                    refine ⟨3185114338071517092522985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16987276469714757826789253 3185114338071517092522985)
                    ·
                      refine ⟨2388835753553637819392239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3185114338071517092522985 2388835753553637819392239)
                      ·
                        rfl

theorem cell23_4652241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 3, 4, 2].length) (baseStart_4652241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4652241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4652241 prefixEnd_4652241 := by exact prefixLift 4652241
  have htrace : WordTrace (prefixWord ++ tailWord_4652241) baseStart_4652241 baseEnd_4652241 := by
    simpa [prefixWord, tailWord_4652241, baseEnd_4652241] using wordTrace_append hprefix tailTrace_4652241
  have hstable : (prefixWord ++ tailWord_4652241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4652241).length < 2 ^ (prefixWord ++ tailWord_4652241).sum := by decide
  have hdescent : baseEnd_4652241 < baseStart_4652241 := by decide
  rcases family_descends (prefixWord ++ tailWord_4652241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4652245 : List Nat := [1, 3, 2, 4, 1, 1, 2, 3, 1, 3, 2]
def baseStart_4652245 : Nat := 118140960795 + 4652245 * 2 ^ 59
def prefixEnd_4652245 : Nat := 4983230072969 + 3 ^ 40 * 4652245 * 2
def baseEnd_4652245 : Nat := 2388837807476255803742221

theorem tailTrace_4652245 : CollatzResearch.WordTrace tailWord_4652245 prefixEnd_4652245 2388837807476255803742221 := by
  unfold tailWord_4652245
  simp only [CollatzResearch.WordTrace]
  refine ⟨169681315030718380034534189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113120876687145586689689459 169681315030718380034534189)
  ·
    refine ⟨63630493136519392512950321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169681315030718380034534189 63630493136519392512950321)
    ·
      refine ⟨47722869852389544384712741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63630493136519392512950321 47722869852389544384712741)
      ·
        refine ⟨8948038097323039572133639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47722869852389544384712741 8948038097323039572133639)
        ·
          refine ⟨13422057145984559358200459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8948038097323039572133639 13422057145984559358200459)
          ·
            refine ⟨20133085718976839037300689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13422057145984559358200459 20133085718976839037300689)
            ·
              refine ⟨15099814289232629277975517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20133085718976839037300689 15099814289232629277975517)
              ·
                refine ⟨5662430358462235979240819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15099814289232629277975517 5662430358462235979240819)
                ·
                  refine ⟨8493645537693353968861229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5662430358462235979240819 8493645537693353968861229)
                  ·
                    refine ⟨3185117076635007738322961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8493645537693353968861229 3185117076635007738322961)
                    ·
                      refine ⟨2388837807476255803742221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3185117076635007738322961 2388837807476255803742221)
                      ·
                        rfl

theorem cell23_4652245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_4652245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4652245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4652245 prefixEnd_4652245 := by exact prefixLift 4652245
  have htrace : WordTrace (prefixWord ++ tailWord_4652245) baseStart_4652245 baseEnd_4652245 := by
    simpa [prefixWord, tailWord_4652245, baseEnd_4652245] using wordTrace_append hprefix tailTrace_4652245
  have hstable : (prefixWord ++ tailWord_4652245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4652245).length < 2 ^ (prefixWord ++ tailWord_4652245).sum := by decide
  have hdescent : baseEnd_4652245 < baseStart_4652245 := by decide
  rcases family_descends (prefixWord ++ tailWord_4652245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4652275 : List Nat := [1, 1, 1, 2, 2, 6, 1, 3, 2, 2, 2]
def baseStart_4652275 : Nat := 118140960795 + 4652275 * 2 ^ 59
def prefixEnd_4652275 : Nat := 4983230072969 + 3 ^ 40 * 4652275 * 2
def baseEnd_4652275 : Nat := 2388853211895890686367083

theorem tailTrace_4652275 : CollatzResearch.WordTrace tailWord_4652275 prefixEnd_4652275 2388853211895890686367083 := by
  unfold tailWord_4652275
  simp only [CollatzResearch.WordTrace]
  refine ⟨169682409220609695158126279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113121606147073130105417519 169682409220609695158126279)
  ·
    refine ⟨254523613830914542737189419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169682409220609695158126279 254523613830914542737189419)
    ·
      refine ⟨381785420746371814105784129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254523613830914542737189419 381785420746371814105784129)
      ·
        refine ⟨286339065559778860579338097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 381785420746371814105784129 286339065559778860579338097)
        ·
          refine ⟨214754299169834145434503573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 286339065559778860579338097 214754299169834145434503573)
          ·
            refine ⟨10066607773585975567242355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 214754299169834145434503573 10066607773585975567242355)
            ·
              refine ⟨15099911660378963350863533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10066607773585975567242355 15099911660378963350863533)
              ·
                refine ⟨5662466872642111256573825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15099911660378963350863533 5662466872642111256573825)
                ·
                  refine ⟨4246850154481583442430369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5662466872642111256573825 4246850154481583442430369)
                  ·
                    refine ⟨3185137615861187581822777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4246850154481583442430369 3185137615861187581822777)
                    ·
                      refine ⟨2388853211895890686367083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3185137615861187581822777 2388853211895890686367083)
                      ·
                        rfl

theorem cell23_4652275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 3, 2, 2, 2].length) (baseStart_4652275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4652275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4652275 prefixEnd_4652275 := by exact prefixLift 4652275
  have htrace : WordTrace (prefixWord ++ tailWord_4652275) baseStart_4652275 baseEnd_4652275 := by
    simpa [prefixWord, tailWord_4652275, baseEnd_4652275] using wordTrace_append hprefix tailTrace_4652275
  have hstable : (prefixWord ++ tailWord_4652275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4652275).length < 2 ^ (prefixWord ++ tailWord_4652275).sum := by decide
  have hdescent : baseEnd_4652275 < baseStart_4652275 := by decide
  rcases family_descends (prefixWord ++ tailWord_4652275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4652311 : List Nat := [1, 1, 3, 4, 1, 1, 1, 4, 2, 5]
def baseStart_4652311 : Nat := 118140960795 + 4652311 * 2 ^ 59
def prefixEnd_4652311 : Nat := 4983230072969 + 3 ^ 40 * 4652311 * 2
def baseEnd_4652311 : Nat := 796290565733150848505639

theorem tailTrace_4652311 : CollatzResearch.WordTrace tailWord_4652311 prefixEnd_4652311 796290565733150848505639 := by
  unfold tailWord_4652311
  simp only [CollatzResearch.WordTrace]
  refine ⟨169683722248479273306436787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113122481498986182204291191 169683722248479273306436787)
  ·
    refine ⟨254525583372718909959655181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169683722248479273306436787 254525583372718909959655181)
    ·
      refine ⟨95447093764769591234870693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 254525583372718909959655181 95447093764769591234870693)
      ·
        refine ⟨17896330080894298356538255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95447093764769591234870693 17896330080894298356538255)
        ·
          refine ⟨26844495121341447534807383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17896330080894298356538255 26844495121341447534807383)
          ·
            refine ⟨40266742682012171302211075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26844495121341447534807383 40266742682012171302211075)
            ·
              refine ⟨60400114023018256953316613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40266742682012171302211075 60400114023018256953316613)
              ·
                refine ⟨11325021379315923178746865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60400114023018256953316613 11325021379315923178746865)
                ·
                  refine ⟨8493766034486942384060149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11325021379315923178746865 8493766034486942384060149)
                  ·
                    refine ⟨796290565733150848505639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8493766034486942384060149 796290565733150848505639)
                    ·
                      rfl

theorem cell23_4652311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 4, 2, 5].length) (baseStart_4652311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4652311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4652311 prefixEnd_4652311 := by exact prefixLift 4652311
  have htrace : WordTrace (prefixWord ++ tailWord_4652311) baseStart_4652311 baseEnd_4652311 := by
    simpa [prefixWord, tailWord_4652311, baseEnd_4652311] using wordTrace_append hprefix tailTrace_4652311
  have hstable : (prefixWord ++ tailWord_4652311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4652311).length < 2 ^ (prefixWord ++ tailWord_4652311).sum := by decide
  have hdescent : baseEnd_4652311 < baseStart_4652311 := by decide
  rcases family_descends (prefixWord ++ tailWord_4652311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4652345 : List Nat := [1, 2, 1, 6, 2, 2, 1, 1, 2, 5]
def baseStart_4652345 : Nat := 118140960795 + 4652345 * 2 ^ 59
def prefixEnd_4652345 : Nat := 4983230072969 + 3 ^ 40 * 4652345 * 2
def baseEnd_4652345 : Nat := 796296385180568470830587

theorem tailTrace_4652345 : CollatzResearch.WordTrace tailWord_4652345 prefixEnd_4652345 796296385180568470830587 := by
  unfold tailWord_4652345
  simp only [CollatzResearch.WordTrace]
  refine ⟨169684962330356097113174489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113123308220237398075449659 169684962330356097113174489)
  ·
    refine ⟨127263721747767072834880867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169684962330356097113174489 127263721747767072834880867)
    ·
      refine ⟨190895582621650609252321301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127263721747767072834880867 190895582621650609252321301)
      ·
        refine ⟨8948230435389872308702561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 190895582621650609252321301 8948230435389872308702561)
        ·
          refine ⟨6711172826542404231526921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8948230435389872308702561 6711172826542404231526921)
          ·
            refine ⟨5033379619906803173645191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6711172826542404231526921 5033379619906803173645191)
            ·
              refine ⟨7550069429860204760467787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5033379619906803173645191 7550069429860204760467787)
              ·
                refine ⟨11325104144790307140701681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7550069429860204760467787 11325104144790307140701681)
                ·
                  refine ⟨8493828108592730355526261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11325104144790307140701681 8493828108592730355526261)
                  ·
                    refine ⟨796296385180568470830587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8493828108592730355526261 796296385180568470830587)
                    ·
                      rfl

theorem cell23_4652345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 1, 2, 5].length) (baseStart_4652345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4652345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4652345 prefixEnd_4652345 := by exact prefixLift 4652345
  have htrace : WordTrace (prefixWord ++ tailWord_4652345) baseStart_4652345 baseEnd_4652345 := by
    simpa [prefixWord, tailWord_4652345, baseEnd_4652345] using wordTrace_append hprefix tailTrace_4652345
  have hstable : (prefixWord ++ tailWord_4652345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4652345).length < 2 ^ (prefixWord ++ tailWord_4652345).sum := by decide
  have hdescent : baseEnd_4652345 < baseStart_4652345 := by decide
  rcases family_descends (prefixWord ++ tailWord_4652345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4652348 : List Nat := [2, 2, 2, 2, 1, 3, 3, 1, 2, 1, 4]
def baseStart_4652348 : Nat := 118140960795 + 4652348 * 2 ^ 59
def prefixEnd_4652348 : Nat := 4983230072969 + 3 ^ 40 * 4652348 * 2
def baseEnd_4652348 : Nat := 2388890695983668900754247

theorem tailTrace_4652348 : CollatzResearch.WordTrace tailWord_4652348 prefixEnd_4652348 2388890695983668900754247 := by
  unfold tailWord_4652348
  simp only [CollatzResearch.WordTrace]
  refine ⟨84842535874672614312766849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113123381166230152417022465 84842535874672614312766849)
  ·
    refine ⟨63631901906004460734575137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84842535874672614312766849 63631901906004460734575137)
    ·
      refine ⟨47723926429503345550931353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63631901906004460734575137 47723926429503345550931353)
      ·
        refine ⟨35792944822127509163198515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47723926429503345550931353 35792944822127509163198515)
        ·
          refine ⟨53689417233191263744797773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35792944822127509163198515 53689417233191263744797773)
          ·
            refine ⟨20133531462446723904299165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53689417233191263744797773 20133531462446723904299165)
            ·
              refine ⟨7550074298417521464112187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20133531462446723904299165 7550074298417521464112187)
              ·
                refine ⟨11325111447626282196168281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7550074298417521464112187 11325111447626282196168281)
                ·
                  refine ⟨8493833585719711647126211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11325111447626282196168281 8493833585719711647126211)
                  ·
                    refine ⟨12740750378579567470689317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8493833585719711647126211 12740750378579567470689317)
                    ·
                      refine ⟨2388890695983668900754247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12740750378579567470689317 2388890695983668900754247)
                      ·
                        rfl

theorem cell23_4652348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 1, 2, 1, 4].length) (baseStart_4652348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4652348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4652348 prefixEnd_4652348 := by exact prefixLift 4652348
  have htrace : WordTrace (prefixWord ++ tailWord_4652348) baseStart_4652348 baseEnd_4652348 := by
    simpa [prefixWord, tailWord_4652348, baseEnd_4652348] using wordTrace_append hprefix tailTrace_4652348
  have hstable : (prefixWord ++ tailWord_4652348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4652348).length < 2 ^ (prefixWord ++ tailWord_4652348).sum := by decide
  have hdescent : baseEnd_4652348 < baseStart_4652348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4652348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4652375 : List Nat := [1, 1, 3, 2, 3, 2, 2, 4, 1, 4]
def baseStart_4652375 : Nat := 118140960795 + 4652375 * 2 ^ 59
def prefixEnd_4652375 : Nat := 4983230072969 + 3 ^ 40 * 4652375 * 2
def baseEnd_4652375 : Nat := 796301519987113431705541

theorem tailTrace_4652375 : CollatzResearch.WordTrace tailWord_4652375 prefixEnd_4652375 796301519987113431705541 := by
  unfold tailWord_4652375
  simp only [CollatzResearch.WordTrace]
  refine ⟨169686056520247412236766579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113124037680164941491177719 169686056520247412236766579)
  ·
    refine ⟨254529084780371118355149869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169686056520247412236766579 254529084780371118355149869)
    ·
      refine ⟨95448406792639169383181201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 254529084780371118355149869 95448406792639169383181201)
      ·
        refine ⟨71586305094479377037385901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95448406792639169383181201 71586305094479377037385901)
        ·
          refine ⟨26844864410429766389019713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71586305094479377037385901 26844864410429766389019713)
          ·
            refine ⟨20133648307822324791764785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26844864410429766389019713 20133648307822324791764785)
            ·
              refine ⟨15100236230866743593823589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20133648307822324791764785 15100236230866743593823589)
              ·
                refine ⟨2831294293287514423841923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15100236230866743593823589 2831294293287514423841923)
                ·
                  refine ⟨4246941439931271635762885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2831294293287514423841923 4246941439931271635762885)
                  ·
                    refine ⟨796301519987113431705541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4246941439931271635762885 796301519987113431705541)
                    ·
                      rfl

theorem cell23_4652375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 4, 1, 4].length) (baseStart_4652375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4652375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4652375 prefixEnd_4652375 := by exact prefixLift 4652375
  have htrace : WordTrace (prefixWord ++ tailWord_4652375) baseStart_4652375 baseEnd_4652375 := by
    simpa [prefixWord, tailWord_4652375, baseEnd_4652375] using wordTrace_append hprefix tailTrace_4652375
  have hstable : (prefixWord ++ tailWord_4652375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4652375).length < 2 ^ (prefixWord ++ tailWord_4652375).sum := by decide
  have hdescent : baseEnd_4652375 < baseStart_4652375 := by decide
  rcases family_descends (prefixWord ++ tailWord_4652375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4652401 : List Nat := [1, 2, 2, 2, 1, 2, 2, 3, 3, 5]
def baseStart_4652401 : Nat := 118140960795 + 4652401 * 2 ^ 59
def prefixEnd_4652401 : Nat := 4983230072969 + 3 ^ 40 * 4652401 * 2
def baseEnd_4652401 : Nat := 796305970152785731130501

theorem tailTrace_4652401 : CollatzResearch.WordTrace tailWord_4652401 prefixEnd_4652401 796305970152785731130501 := by
  unfold tailWord_4652401
  simp only [CollatzResearch.WordTrace]
  refine ⟨169687004818153218677213057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113124669878768812451475371 169687004818153218677213057)
  ·
    refine ⟨127265253613614914007909793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169687004818153218677213057 127265253613614914007909793)
    ·
      refine ⟨95448940210211185505932345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127265253613614914007909793 95448940210211185505932345)
      ·
        refine ⟨71586705157658389129449259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95448940210211185505932345 71586705157658389129449259)
        ·
          refine ⟨107380057736487583694173889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71586705157658389129449259 107380057736487583694173889)
          ·
            refine ⟨80535043302365687770630417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107380057736487583694173889 80535043302365687770630417)
            ·
              refine ⟨60401282476774265827972813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80535043302365687770630417 60401282476774265827972813)
              ·
                refine ⟨22650480928790349685489805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60401282476774265827972813 22650480928790349685489805)
                ·
                  refine ⟨8493930348296381132058677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22650480928790349685489805 8493930348296381132058677)
                  ·
                    refine ⟨796305970152785731130501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8493930348296381132058677 796305970152785731130501)
                    ·
                      rfl

theorem cell23_4652401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 3, 5].length) (baseStart_4652401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4652401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4652401 prefixEnd_4652401 := by exact prefixLift 4652401
  have htrace : WordTrace (prefixWord ++ tailWord_4652401) baseStart_4652401 baseEnd_4652401 := by
    simpa [prefixWord, tailWord_4652401, baseEnd_4652401] using wordTrace_append hprefix tailTrace_4652401
  have hstable : (prefixWord ++ tailWord_4652401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4652401).length < 2 ^ (prefixWord ++ tailWord_4652401).sum := by decide
  have hdescent : baseEnd_4652401 < baseStart_4652401 := by decide
  rcases family_descends (prefixWord ++ tailWord_4652401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4652408 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 8, 3, 2]
def baseStart_4652408 : Nat := 118140960795 + 4652408 * 2 ^ 59
def prefixEnd_4652408 : Nat := 4983230072969 + 3 ^ 40 * 4652408 * 2
def baseEnd_4652408 : Nat := 2388921504822938666003971

theorem tailTrace_4652408 : CollatzResearch.WordTrace tailWord_4652408 prefixEnd_4652408 2388921504822938666003971 := by
  unfold tailWord_4652408
  simp only [CollatzResearch.WordTrace]
  refine ⟨84843630064563929436358939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113124840086085239248478585 84843630064563929436358939)
  ·
    refine ⟨127265445096845894154538409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84843630064563929436358939 127265445096845894154538409)
    ·
      refine ⟨95449083822634420615903807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127265445096845894154538409 95449083822634420615903807)
      ·
        refine ⟨143173625733951630923855711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95449083822634420615903807 143173625733951630923855711)
        ·
          refine ⟨214760438600927446385783567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143173625733951630923855711 214760438600927446385783567)
          ·
            refine ⟨322140657901391169578675351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214760438600927446385783567 322140657901391169578675351)
            ·
              refine ⟨483210986852086754368013027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 322140657901391169578675351 483210986852086754368013027)
              ·
                refine ⟨724816480278130131552019541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 483210986852086754368013027 724816480278130131552019541)
                ·
                  refine ⟨8493943128259337479125229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 724816480278130131552019541 8493943128259337479125229)
                  ·
                    refine ⟨3185228673097251554671961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8493943128259337479125229 3185228673097251554671961)
                    ·
                      refine ⟨2388921504822938666003971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3185228673097251554671961 2388921504822938666003971)
                      ·
                        rfl

theorem cell23_4652408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 8, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 8, 3, 2].length) (baseStart_4652408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4652408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4652408 prefixEnd_4652408 := by exact prefixLift 4652408
  have htrace : WordTrace (prefixWord ++ tailWord_4652408) baseStart_4652408 baseEnd_4652408 := by
    simpa [prefixWord, tailWord_4652408, baseEnd_4652408] using wordTrace_append hprefix tailTrace_4652408
  have hstable : (prefixWord ++ tailWord_4652408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4652408).length < 2 ^ (prefixWord ++ tailWord_4652408).sum := by decide
  have hdescent : baseEnd_4652408 < baseStart_4652408 := by decide
  rcases family_descends (prefixWord ++ tailWord_4652408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4652451 : List Nat := [1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 6]
def baseStart_4652451 : Nat := 118140960795 + 4652451 * 2 ^ 59
def prefixEnd_4652451 : Nat := 4983230072969 + 3 ^ 40 * 4652451 * 2
def baseEnd_4652451 : Nat := 2388943584491081997766273

theorem tailTrace_4652451 : CollatzResearch.WordTrace tailWord_4652451 prefixEnd_4652451 2388943584491081997766273 := by
  unfold tailWord_4652451
  simp only [CollatzResearch.WordTrace]
  refine ⟨169688828467972077216533207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113125885645314718144355471 169688828467972077216533207)
  ·
    refine ⟨254533242701958115824799811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169688828467972077216533207 254533242701958115824799811)
    ·
      refine ⟨381799864052937173737199717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254533242701958115824799811 381799864052937173737199717)
      ·
        refine ⟨71587474509925720075724947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 381799864052937173737199717 71587474509925720075724947)
        ·
          refine ⟨107381211764888580113587421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71587474509925720075724947 107381211764888580113587421)
          ·
            refine ⟨40267954411833217542595283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107381211764888580113587421 40267954411833217542595283)
            ·
              refine ⟨60401931617749826313892925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40267954411833217542595283 60401931617749826313892925)
              ·
                refine ⟨22650724356656184867709847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60401931617749826313892925 22650724356656184867709847)
                ·
                  refine ⟨33976086534984277301564771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22650724356656184867709847 33976086534984277301564771)
                  ·
                    refine ⟨50964129802476415952347157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33976086534984277301564771 50964129802476415952347157)
                    ·
                      refine ⟨2388943584491081997766273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50964129802476415952347157 2388943584491081997766273)
                      ·
                        rfl

theorem cell23_4652451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 6].length) (baseStart_4652451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4652451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4652451 prefixEnd_4652451 := by exact prefixLift 4652451
  have htrace : WordTrace (prefixWord ++ tailWord_4652451) baseStart_4652451 baseEnd_4652451 := by
    simpa [prefixWord, tailWord_4652451, baseEnd_4652451] using wordTrace_append hprefix tailTrace_4652451
  have hstable : (prefixWord ++ tailWord_4652451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4652451).length < 2 ^ (prefixWord ++ tailWord_4652451).sum := by decide
  have hdescent : baseEnd_4652451 < baseStart_4652451 := by decide
  rcases family_descends (prefixWord ++ tailWord_4652451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4652488 : List Nat := [2, 1, 3, 1, 3, 1, 1, 2, 3, 3, 3]
def baseStart_4652488 : Nat := 118140960795 + 4652488 * 2 ^ 59
def prefixEnd_4652488 : Nat := 4983230072969 + 3 ^ 40 * 4652488 * 2
def baseEnd_4652488 : Nat := 2388962583275298353003603

theorem tailTrace_4652488 : CollatzResearch.WordTrace tailWord_4652488 prefixEnd_4652488 2388962583275298353003603 := by
  unfold tailWord_4652488
  simp only [CollatzResearch.WordTrace]
  refine ⟨84845088984419016267815059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113126785312558688357086745 84845088984419016267815059)
  ·
    refine ⟨127267633476628524401722589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84845088984419016267815059 127267633476628524401722589)
    ·
      refine ⟨47725362553735696650645971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127267633476628524401722589 47725362553735696650645971)
      ·
        refine ⟨71588043830603544975968957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47725362553735696650645971 71588043830603544975968957)
        ·
          refine ⟨26845516436476329365988359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71588043830603544975968957 26845516436476329365988359)
          ·
            refine ⟨40268274654714494048982539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26845516436476329365988359 40268274654714494048982539)
            ·
              refine ⟨60402411982071741073473809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40268274654714494048982539 60402411982071741073473809)
              ·
                refine ⟨45301808986553805805105357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60402411982071741073473809 45301808986553805805105357)
                ·
                  refine ⟨16988178369957677176914509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45301808986553805805105357 16988178369957677176914509)
                  ·
                    refine ⟨6370566888734128941342941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16988178369957677176914509 6370566888734128941342941)
                    ·
                      refine ⟨2388962583275298353003603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6370566888734128941342941 2388962583275298353003603)
                      ·
                        rfl

theorem cell23_4652488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 3, 3, 3].length) (baseStart_4652488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4652488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4652488 prefixEnd_4652488 := by exact prefixLift 4652488
  have htrace : WordTrace (prefixWord ++ tailWord_4652488) baseStart_4652488 baseEnd_4652488 := by
    simpa [prefixWord, tailWord_4652488, baseEnd_4652488] using wordTrace_append hprefix tailTrace_4652488
  have hstable : (prefixWord ++ tailWord_4652488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4652488).length < 2 ^ (prefixWord ++ tailWord_4652488).sum := by decide
  have hdescent : baseEnd_4652488 < baseStart_4652488 := by decide
  rcases family_descends (prefixWord ++ tailWord_4652488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4652491 : List Nat := [1, 1, 1, 1, 3, 3, 3, 1, 2, 7]
def baseStart_4652491 : Nat := 118140960795 + 4652491 * 2 ^ 59
def prefixEnd_4652491 : Nat := 4983230072969 + 3 ^ 40 * 4652491 * 2
def baseEnd_4652491 : Nat := 796321374572420613755363

theorem tailTrace_4652491 : CollatzResearch.WordTrace tailWord_4652491 prefixEnd_4652491 796321374572420613755363 := by
  unfold tailWord_4652491
  simp only [CollatzResearch.WordTrace]
  refine ⟨169690287387827164047989327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113126858258551442698659551 169690287387827164047989327)
  ·
    refine ⟨254535431081740746071983991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169690287387827164047989327 254535431081740746071983991)
    ·
      refine ⟨381803146622611119107975987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254535431081740746071983991 381803146622611119107975987)
      ·
        refine ⟨572704719933916678661963981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 381803146622611119107975987 572704719933916678661963981)
        ·
          refine ⟨214764269975218754498236493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 572704719933916678661963981 214764269975218754498236493)
          ·
            refine ⟨80536601240707032936838685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 214764269975218754498236493 80536601240707032936838685)
            ·
              refine ⟨30201225465265137351314507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80536601240707032936838685 30201225465265137351314507)
              ·
                refine ⟨45301838197897706026971761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30201225465265137351314507 45301838197897706026971761)
                ·
                  refine ⟨33976378648423279520228821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45301838197897706026971761 33976378648423279520228821)
                  ·
                    refine ⟨796321374572420613755363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33976378648423279520228821 796321374572420613755363)
                    ·
                      rfl

theorem cell23_4652491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 7].length) (baseStart_4652491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4652491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4652491 prefixEnd_4652491 := by exact prefixLift 4652491
  have htrace : WordTrace (prefixWord ++ tailWord_4652491) baseStart_4652491 baseEnd_4652491 := by
    simpa [prefixWord, tailWord_4652491, baseEnd_4652491] using wordTrace_append hprefix tailTrace_4652491
  have hstable : (prefixWord ++ tailWord_4652491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4652491).length < 2 ^ (prefixWord ++ tailWord_4652491).sum := by decide
  have hdescent : baseEnd_4652491 < baseStart_4652491 := by decide
  rcases family_descends (prefixWord ++ tailWord_4652491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4652502 : List Nat := [5, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4]
def baseStart_4652502 : Nat := 118140960795 + 4652502 * 2 ^ 59
def prefixEnd_4652502 : Nat := 4983230072969 + 3 ^ 40 * 4652502 * 2
def baseEnd_4652502 : Nat := 2388969772004461298228539

theorem tailTrace_4652502 : CollatzResearch.WordTrace tailWord_4652502 prefixEnd_4652502 2388969772004461298228539 := by
  unfold tailWord_4652502
  simp only [CollatzResearch.WordTrace]
  refine ⟨10605668036924207057914985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 113127125727191541951093173 10605668036924207057914985)
  ·
    refine ⟨7954251027693155293436239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10605668036924207057914985 7954251027693155293436239)
    ·
      refine ⟨11931376541539732940154359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7954251027693155293436239 11931376541539732940154359)
      ·
        refine ⟨17897064812309599410231539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11931376541539732940154359 17897064812309599410231539)
        ·
          refine ⟨26845597218464399115347309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17897064812309599410231539 26845597218464399115347309)
          ·
            refine ⟨10067098956924149668255241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26845597218464399115347309 10067098956924149668255241)
            ·
              refine ⟨7550324217693112251191431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10067098956924149668255241 7550324217693112251191431)
              ·
                refine ⟨11325486326539668376787147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7550324217693112251191431 11325486326539668376787147)
                ·
                  refine ⟨16988229489809502565180721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11325486326539668376787147 16988229489809502565180721)
                  ·
                    refine ⟨12741172117357126923885541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16988229489809502565180721 12741172117357126923885541)
                    ·
                      refine ⟨2388969772004461298228539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12741172117357126923885541 2388969772004461298228539)
                      ·
                        rfl

theorem cell23_4652502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_4652502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4652502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4652502 prefixEnd_4652502 := by exact prefixLift 4652502
  have htrace : WordTrace (prefixWord ++ tailWord_4652502) baseStart_4652502 baseEnd_4652502 := by
    simpa [prefixWord, tailWord_4652502, baseEnd_4652502] using wordTrace_append hprefix tailTrace_4652502
  have hstable : (prefixWord ++ tailWord_4652502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4652502).length < 2 ^ (prefixWord ++ tailWord_4652502).sum := by decide
  have hdescent : baseEnd_4652502 < baseStart_4652502 := by decide
  rcases family_descends (prefixWord ++ tailWord_4652502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4652505 : List Nat := [1, 2, 1, 2, 4, 3, 2, 1, 1, 3, 3]
def baseStart_4652505 : Nat := 118140960795 + 4652505 * 2 ^ 59
def prefixEnd_4652505 : Nat := 4983230072969 + 3 ^ 40 * 4652505 * 2
def baseEnd_4652505 : Nat := 2388971312446424786491025

theorem tailTrace_4652505 : CollatzResearch.WordTrace tailWord_4652505 prefixEnd_4652505 2388971312446424786491025 := by
  unfold tailWord_4652505
  simp only [CollatzResearch.WordTrace]
  refine ⟨169690798009776444438998969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113127198673184296292665979 169690798009776444438998969)
  ·
    refine ⟨127268098507332333329249227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169690798009776444438998969 127268098507332333329249227)
    ·
      refine ⟨190902147760998499993873841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127268098507332333329249227 190902147760998499993873841)
      ·
        refine ⟨143176610820748874995405381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190902147760998499993873841 143176610820748874995405381)
        ·
          refine ⟨26845614528890414061638509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 143176610820748874995405381 26845614528890414061638509)
          ·
            refine ⟨10067105448333905273114441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26845614528890414061638509 10067105448333905273114441)
            ·
              refine ⟨7550329086250428954835831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10067105448333905273114441 7550329086250428954835831)
              ·
                refine ⟨11325493629375643432253747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7550329086250428954835831 11325493629375643432253747)
                ·
                  refine ⟨16988240444063465148380621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11325493629375643432253747 16988240444063465148380621)
                  ·
                    refine ⟨6370590166523799430642733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16988240444063465148380621 6370590166523799430642733)
                    ·
                      refine ⟨2388971312446424786491025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6370590166523799430642733 2388971312446424786491025)
                      ·
                        rfl

theorem cell23_4652505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 1, 1, 3, 3].length) (baseStart_4652505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4652505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4652505 prefixEnd_4652505 := by exact prefixLift 4652505
  have htrace : WordTrace (prefixWord ++ tailWord_4652505) baseStart_4652505 baseEnd_4652505 := by
    simpa [prefixWord, tailWord_4652505, baseEnd_4652505] using wordTrace_append hprefix tailTrace_4652505
  have hstable : (prefixWord ++ tailWord_4652505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4652505).length < 2 ^ (prefixWord ++ tailWord_4652505).sum := by decide
  have hdescent : baseEnd_4652505 < baseStart_4652505 := by decide
  rcases family_descends (prefixWord ++ tailWord_4652505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4652574 : List Nat := [4, 3, 3, 1, 2, 1, 1, 3, 1, 2, 2]
def baseStart_4652574 : Nat := 118140960795 + 4652574 * 2 ^ 59
def prefixEnd_4652574 : Nat := 4983230072969 + 3 ^ 40 * 4652574 * 2
def baseEnd_4652574 : Nat := 2389006742611585016528209

theorem tailTrace_4652574 : CollatzResearch.WordTrace tailWord_4652574 prefixEnd_4652574 2389006742611585016528209 := by
  unfold tailWord_4652574
  simp only [CollatzResearch.WordTrace]
  refine ⟨21211664330815808652907597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113128876431017646148840517 21211664330815808652907597)
  ·
    refine ⟨7954374124055928244840349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21211664330815808652907597 7954374124055928244840349)
    ·
      refine ⟨2982890296520973091815131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7954374124055928244840349 2982890296520973091815131)
      ·
        refine ⟨4474335444781459637722697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2982890296520973091815131 4474335444781459637722697)
        ·
          refine ⟨3355751583586094728292023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4474335444781459637722697 3355751583586094728292023)
          ·
            refine ⟨5033627375379142092438035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3355751583586094728292023 5033627375379142092438035)
            ·
              refine ⟨7550441063068713138657053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5033627375379142092438035 7550441063068713138657053)
              ·
                refine ⟨2831415398650767426996395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7550441063068713138657053 2831415398650767426996395)
                ·
                  refine ⟨4247123097976151140494593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2831415398650767426996395 4247123097976151140494593)
                  ·
                    refine ⟨3185342323482113355370945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4247123097976151140494593 3185342323482113355370945)
                    ·
                      refine ⟨2389006742611585016528209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3185342323482113355370945 2389006742611585016528209)
                      ·
                        rfl

theorem cell23_4652574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_4652574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4652574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4652574 prefixEnd_4652574 := by exact prefixLift 4652574
  have htrace : WordTrace (prefixWord ++ tailWord_4652574) baseStart_4652574 baseEnd_4652574 := by
    simpa [prefixWord, tailWord_4652574, baseEnd_4652574] using wordTrace_append hprefix tailTrace_4652574
  have hstable : (prefixWord ++ tailWord_4652574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4652574).length < 2 ^ (prefixWord ++ tailWord_4652574).sum := by decide
  have hdescent : baseEnd_4652574 < baseStart_4652574 := by decide
  rcases family_descends (prefixWord ++ tailWord_4652574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4652602 : List Nat := [3, 1, 1, 1, 3, 2, 5, 2, 5]
def baseStart_4652602 : Nat := 118140960795 + 4652602 * 2 ^ 59
def prefixEnd_4652602 : Nat := 4983230072969 + 3 ^ 40 * 4652602 * 2
def baseEnd_4652602 : Nat := 265446791118878989664231

theorem tailTrace_4652602 : CollatzResearch.WordTrace tailWord_4652602 prefixEnd_4652602 265446791118878989664231 := by
  unfold tailWord_4652602
  simp only [CollatzResearch.WordTrace]
  refine ⟨42423583972606257501320015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113129557260283353336853373 42423583972606257501320015)
  ·
    refine ⟨63635375958909386251980023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42423583972606257501320015 63635375958909386251980023)
    ·
      refine ⟨95453063938364079377970035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63635375958909386251980023 95453063938364079377970035)
      ·
        refine ⟨143179595907546119066955053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95453063938364079377970035 143179595907546119066955053)
        ·
          refine ⟨53692348465329794650108145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 143179595907546119066955053 53692348465329794650108145)
          ·
            refine ⟨40269261348997345987581109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53692348465329794650108145 40269261348997345987581109)
            ·
              refine ⟨3775243251468501186335729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40269261348997345987581109 3775243251468501186335729)
              ·
                refine ⟨2831432438601375889751797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3775243251468501186335729 2831432438601375889751797)
                ·
                  refine ⟨265446791118878989664231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2831432438601375889751797 265446791118878989664231)
                  ·
                    rfl

theorem cell23_4652602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 5, 2, 5].length) (baseStart_4652602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4652602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4652602 prefixEnd_4652602 := by exact prefixLift 4652602
  have htrace : WordTrace (prefixWord ++ tailWord_4652602) baseStart_4652602 baseEnd_4652602 := by
    simpa [prefixWord, tailWord_4652602, baseEnd_4652602] using wordTrace_append hprefix tailTrace_4652602
  have hstable : (prefixWord ++ tailWord_4652602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4652602).length < 2 ^ (prefixWord ++ tailWord_4652602).sum := by decide
  have hdescent : baseEnd_4652602 < baseStart_4652602 := by decide
  rcases family_descends (prefixWord ++ tailWord_4652602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4652719 : List Nat := [1, 1, 2, 1, 2, 4, 1, 6, 1, 1, 3]
def baseStart_4652719 : Nat := 118140960795 + 4652719 * 2 ^ 59
def prefixEnd_4652719 : Nat := 4983230072969 + 3 ^ 40 * 4652719 * 2
def baseEnd_4652719 : Nat := 2389081197306486949215041

theorem tailTrace_4652719 : CollatzResearch.WordTrace tailWord_4652719 prefixEnd_4652719 2389081197306486949215041 := by
  unfold tailWord_4652719
  simp only [CollatzResearch.WordTrace]
  refine ⟨169698603231001158987289211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113132402154000772658192807 169698603231001158987289211)
  ·
    refine ⟨254547904846501738480933817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169698603231001158987289211 254547904846501738480933817)
    ·
      refine ⟨190910928634876303860700363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 254547904846501738480933817 190910928634876303860700363)
      ·
        refine ⟨286366392952314455791050545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190910928634876303860700363 286366392952314455791050545)
        ·
          refine ⟨214774794714235841843287909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 286366392952314455791050545 214774794714235841843287909)
          ·
            refine ⟨40270274008919220345616483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 214774794714235841843287909 40270274008919220345616483)
            ·
              refine ⟨60405411013378830518424725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40270274008919220345616483 60405411013378830518424725)
              ·
                refine ⟨2831503641252132680551159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 60405411013378830518424725 2831503641252132680551159)
                ·
                  refine ⟨4247255461878199020826739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2831503641252132680551159 4247255461878199020826739)
                  ·
                    refine ⟨6370883192817298531240109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4247255461878199020826739 6370883192817298531240109)
                    ·
                      refine ⟨2389081197306486949215041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6370883192817298531240109 2389081197306486949215041)
                      ·
                        rfl

theorem cell23_4652719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 6, 1, 1, 3].length) (baseStart_4652719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4652719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4652719 prefixEnd_4652719 := by exact prefixLift 4652719
  have htrace : WordTrace (prefixWord ++ tailWord_4652719) baseStart_4652719 baseEnd_4652719 := by
    simpa [prefixWord, tailWord_4652719, baseEnd_4652719] using wordTrace_append hprefix tailTrace_4652719
  have hstable : (prefixWord ++ tailWord_4652719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4652719).length < 2 ^ (prefixWord ++ tailWord_4652719).sum := by decide
  have hdescent : baseEnd_4652719 < baseStart_4652719 := by decide
  rcases family_descends (prefixWord ++ tailWord_4652719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4652726 : List Nat := [5, 1, 3, 1, 1, 2, 3, 1, 6]
def baseStart_4652726 : Nat := 118140960795 + 4652726 * 2 ^ 59
def prefixEnd_4652726 : Nat := 4983230072969 + 3 ^ 40 * 4652726 * 2
def baseEnd_4652726 : Nat := 265453865741229824647501

theorem tailTrace_4652726 : CollatzResearch.WordTrace tailWord_4652726 prefixEnd_4652726 265453865741229824647501 := by
  unfold tailWord_4652726
  simp only [CollatzResearch.WordTrace]
  refine ⟨10606178658873487448924627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 113132572361317199455196021 10606178658873487448924627)
  ·
    refine ⟨15909267988310231173386941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10606178658873487448924627 15909267988310231173386941)
    ·
      refine ⟨5965975495616336690020103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15909267988310231173386941 5965975495616336690020103)
      ·
        refine ⟨8948963243424505035030155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5965975495616336690020103 8948963243424505035030155)
        ·
          refine ⟨13423444865136757552545233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8948963243424505035030155 13423444865136757552545233)
          ·
            refine ⟨10067583648852568164408925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13423444865136757552545233 10067583648852568164408925)
            ·
              refine ⟨3775343868319713061653347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10067583648852568164408925 3775343868319713061653347)
              ·
                refine ⟨5663015802479569592480021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3775343868319713061653347 5663015802479569592480021)
                ·
                  refine ⟨265453865741229824647501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5663015802479569592480021 265453865741229824647501)
                  ·
                    rfl

theorem cell23_4652726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 3, 1, 6].length) (baseStart_4652726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4652726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4652726 prefixEnd_4652726 := by exact prefixLift 4652726
  have htrace : WordTrace (prefixWord ++ tailWord_4652726) baseStart_4652726 baseEnd_4652726 := by
    simpa [prefixWord, tailWord_4652726, baseEnd_4652726] using wordTrace_append hprefix tailTrace_4652726
  have hstable : (prefixWord ++ tailWord_4652726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4652726).length < 2 ^ (prefixWord ++ tailWord_4652726).sum := by decide
  have hdescent : baseEnd_4652726 < baseStart_4652726 := by decide
  rcases family_descends (prefixWord ++ tailWord_4652726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4652762 : List Nat := [3, 1, 1, 2, 2, 4, 2, 1, 1, 1, 5]
def baseStart_4652762 : Nat := 118140960795 + 4652762 * 2 ^ 59
def prefixEnd_4652762 : Nat := 4983230072969 + 3 ^ 40 * 4652762 * 2
def baseEnd_4652762 : Nat := 2389103276974630280977343

theorem tailTrace_4652762 : CollatzResearch.WordTrace tailWord_4652762 prefixEnd_4652762 2389103276974630280977343 := by
  unfold tailWord_4652762
  simp only [CollatzResearch.WordTrace]
  refine ⟨42425042892461344332776135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113133447713230251554069693 42425042892461344332776135)
  ·
    refine ⟨63637564338692016499164203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42425042892461344332776135 63637564338692016499164203)
    ·
      refine ⟨95456346508038024748746305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63637564338692016499164203 95456346508038024748746305)
      ·
        refine ⟨71592259881028518561559729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95456346508038024748746305 71592259881028518561559729)
        ·
          refine ⟨53694194910771388921169797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71592259881028518561559729 53694194910771388921169797)
          ·
            refine ⟨10067661545769635422719337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53694194910771388921169797 10067661545769635422719337)
            ·
              refine ⟨7550746159327226567039503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10067661545769635422719337 7550746159327226567039503)
              ·
                refine ⟨11326119238990839850559255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7550746159327226567039503 11326119238990839850559255)
                ·
                  refine ⟨16989178858486259775838883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11326119238990839850559255 16989178858486259775838883)
                  ·
                    refine ⟨25483768287729389663758325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16989178858486259775838883 25483768287729389663758325)
                    ·
                      refine ⟨2389103276974630280977343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25483768287729389663758325 2389103276974630280977343)
                      ·
                        rfl

theorem cell23_4652762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 1, 1, 1, 5].length) (baseStart_4652762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4652762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4652762 prefixEnd_4652762 := by exact prefixLift 4652762
  have htrace : WordTrace (prefixWord ++ tailWord_4652762) baseStart_4652762 baseEnd_4652762 := by
    simpa [prefixWord, tailWord_4652762, baseEnd_4652762] using wordTrace_append hprefix tailTrace_4652762
  have hstable : (prefixWord ++ tailWord_4652762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4652762).length < 2 ^ (prefixWord ++ tailWord_4652762).sum := by decide
  have hdescent : baseEnd_4652762 < baseStart_4652762 := by decide
  rcases family_descends (prefixWord ++ tailWord_4652762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4652776 : List Nat := [2, 1, 4, 1, 3, 1, 3, 1, 3, 2, 2]
def baseStart_4652776 : Nat := 118140960795 + 4652776 * 2 ^ 59
def prefixEnd_4652776 : Nat := 4983230072969 + 3 ^ 40 * 4652776 * 2
def baseEnd_4652776 : Nat := 2389110465703793226202279

theorem tailTrace_4652776 : CollatzResearch.WordTrace tailWord_4652776 prefixEnd_4652776 2389110465703793226202279 := by
  unfold tailWord_4652776
  simp only [CollatzResearch.WordTrace]
  refine ⟨84850341095897328861057091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113133788127863105148076121 84850341095897328861057091)
  ·
    refine ⟨127275511643845993291585637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84850341095897328861057091 127275511643845993291585637)
    ·
      refine ⟨23864158433221123742172307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127275511643845993291585637 23864158433221123742172307)
      ·
        refine ⟨35796237649831685613258461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23864158433221123742172307 35796237649831685613258461)
        ·
          refine ⟨13423589118686882104971923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35796237649831685613258461 13423589118686882104971923)
          ·
            refine ⟨20135383678030323157457885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13423589118686882104971923 20135383678030323157457885)
            ·
              refine ⟨7550768879261371184046707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20135383678030323157457885 7550768879261371184046707)
              ·
                refine ⟨11326153318892056776070061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7550768879261371184046707 11326153318892056776070061)
                ·
                  refine ⟨4247307494584521291026273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11326153318892056776070061 4247307494584521291026273)
                  ·
                    refine ⟨3185480620938390968269705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4247307494584521291026273 3185480620938390968269705)
                    ·
                      refine ⟨2389110465703793226202279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3185480620938390968269705 2389110465703793226202279)
                      ·
                        rfl

theorem cell23_4652776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 1, 3, 2, 2].length) (baseStart_4652776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4652776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4652776 prefixEnd_4652776 := by exact prefixLift 4652776
  have htrace : WordTrace (prefixWord ++ tailWord_4652776) baseStart_4652776 baseEnd_4652776 := by
    simpa [prefixWord, tailWord_4652776, baseEnd_4652776] using wordTrace_append hprefix tailTrace_4652776
  have hstable : (prefixWord ++ tailWord_4652776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4652776).length < 2 ^ (prefixWord ++ tailWord_4652776).sum := by decide
  have hdescent : baseEnd_4652776 < baseStart_4652776 := by decide
  rcases family_descends (prefixWord ++ tailWord_4652776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4652792 : List Nat := [2, 1, 2, 1, 1, 2, 2, 2, 6, 1, 3]
def baseStart_4652792 : Nat := 118140960795 + 4652792 * 2 ^ 59
def prefixEnd_4652792 : Nat := 4983230072969 + 3 ^ 40 * 4652792 * 2
def baseEnd_4652792 : Nat := 2389118681394265163602205

theorem tailTrace_4652792 : CollatzResearch.WordTrace tailWord_4652792 prefixEnd_4652792 2389118681394265163602205 := by
  unfold tailWord_4652792
  simp only [CollatzResearch.WordTrace]
  refine ⟨84850632879868346227348315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113134177173157794969797753 84850632879868346227348315)
  ·
    refine ⟨127275949319802519341022473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84850632879868346227348315 127275949319802519341022473)
    ·
      refine ⟨95456961989851889505766855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127275949319802519341022473 95456961989851889505766855)
      ·
        refine ⟨143185442984777834258650283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95456961989851889505766855 143185442984777834258650283)
        ·
          refine ⟨214778164477166751387975425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143185442984777834258650283 214778164477166751387975425)
          ·
            refine ⟨161083623357875063540981569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 214778164477166751387975425 161083623357875063540981569)
            ·
              refine ⟨120812717518406297655736177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 161083623357875063540981569 120812717518406297655736177)
              ·
                refine ⟨90609538138804723241802133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 120812717518406297655736177 90609538138804723241802133)
                ·
                  refine ⟨4247322100256471401959475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 90609538138804723241802133 4247322100256471401959475)
                  ·
                    refine ⟨6370983150384707102939213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4247322100256471401959475 6370983150384707102939213)
                    ·
                      refine ⟨2389118681394265163602205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6370983150384707102939213 2389118681394265163602205)
                      ·
                        rfl

theorem cell23_4652792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 6, 1, 3].length) (baseStart_4652792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4652792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4652792 prefixEnd_4652792 := by exact prefixLift 4652792
  have htrace : WordTrace (prefixWord ++ tailWord_4652792) baseStart_4652792 baseEnd_4652792 := by
    simpa [prefixWord, tailWord_4652792, baseEnd_4652792] using wordTrace_append hprefix tailTrace_4652792
  have hstable : (prefixWord ++ tailWord_4652792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4652792).length < 2 ^ (prefixWord ++ tailWord_4652792).sum := by decide
  have hdescent : baseEnd_4652792 < baseStart_4652792 := by decide
  rcases family_descends (prefixWord ++ tailWord_4652792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4652820 : List Nat := [2, 4, 4, 1, 1, 1, 2, 2, 2, 4]
def baseStart_4652820 : Nat := 118140960795 + 4652820 * 2 ^ 59
def prefixEnd_4652820 : Nat := 4983230072969 + 3 ^ 40 * 4652820 * 2
def baseEnd_4652820 : Nat := 796377686284197018017359

theorem tailTrace_4652820 : CollatzResearch.WordTrace tailWord_4652820 prefixEnd_4652820 796377686284197018017359 := by
  unfold tailWord_4652820
  simp only [CollatzResearch.WordTrace]
  refine ⟨84851143501817626618357957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113134858002423502157810609 84851143501817626618357957)
  ·
    refine ⟨15909589406590804990942117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84851143501817626618357957 15909589406590804990942117)
    ·
      refine ⟨2983048013735775935801647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15909589406590804990942117 2983048013735775935801647)
      ·
        refine ⟨4474572020603663903702471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2983048013735775935801647 4474572020603663903702471)
        ·
          refine ⟨6711858030905495855553707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4474572020603663903702471 6711858030905495855553707)
          ·
            refine ⟨10067787046358243783330561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6711858030905495855553707 10067787046358243783330561)
            ·
              refine ⟨7550840284768682837497921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10067787046358243783330561 7550840284768682837497921)
              ·
                refine ⟨5663130213576512128123441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7550840284768682837497921 5663130213576512128123441)
                ·
                  refine ⟨4247347660182384096092581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5663130213576512128123441 4247347660182384096092581)
                  ·
                    refine ⟨796377686284197018017359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4247347660182384096092581 796377686284197018017359)
                    ·
                      rfl

theorem cell23_4652820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_4652820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4652820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4652820 prefixEnd_4652820 := by exact prefixLift 4652820
  have htrace : WordTrace (prefixWord ++ tailWord_4652820) baseStart_4652820 baseEnd_4652820 := by
    simpa [prefixWord, tailWord_4652820, baseEnd_4652820] using wordTrace_append hprefix tailTrace_4652820
  have hstable : (prefixWord ++ tailWord_4652820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4652820).length < 2 ^ (prefixWord ++ tailWord_4652820).sum := by decide
  have hdescent : baseEnd_4652820 < baseStart_4652820 := by decide
  rcases family_descends (prefixWord ++ tailWord_4652820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4652826 : List Nat := [3, 1, 1, 3, 2, 3, 2, 2, 2, 1, 3]
def baseStart_4652826 : Nat := 118140960795 + 4652826 * 2 ^ 59
def prefixEnd_4652826 : Nat := 4983230072969 + 3 ^ 40 * 4652826 * 2
def baseEnd_4652826 : Nat := 2389136139736518030577049

theorem tailTrace_4652826 : CollatzResearch.WordTrace tailWord_4652826 prefixEnd_4652826 2389136139736518030577049 := by
  unfold tailWord_4652826
  simp only [CollatzResearch.WordTrace]
  refine ⟨42425626460403379065358583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113135003894409010840956221 42425626460403379065358583)
  ·
    refine ⟨63638439690605068598037875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42425626460403379065358583 63638439690605068598037875)
    ·
      refine ⟨95457659535907602897056813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63638439690605068598037875 95457659535907602897056813)
      ·
        refine ⟨35796622325965351086396305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95457659535907602897056813 35796622325965351086396305)
        ·
          refine ⟨26847466744474013314797229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35796622325965351086396305 26847466744474013314797229)
          ·
            refine ⟨10067800029177754993048961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26847466744474013314797229 10067800029177754993048961)
            ·
              refine ⟨7550850021883316244786721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10067800029177754993048961 7550850021883316244786721)
              ·
                refine ⟨5663137516412487183590041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7550850021883316244786721 5663137516412487183590041)
                ·
                  refine ⟨4247353137309365387692531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5663137516412487183590041 4247353137309365387692531)
                  ·
                    refine ⟨6371029705964048081538797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4247353137309365387692531 6371029705964048081538797)
                    ·
                      refine ⟨2389136139736518030577049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6371029705964048081538797 2389136139736518030577049)
                      ·
                        rfl

theorem cell23_4652826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 2, 2, 1, 3].length) (baseStart_4652826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4652826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4652826 prefixEnd_4652826 := by exact prefixLift 4652826
  have htrace : WordTrace (prefixWord ++ tailWord_4652826) baseStart_4652826 baseEnd_4652826 := by
    simpa [prefixWord, tailWord_4652826, baseEnd_4652826] using wordTrace_append hprefix tailTrace_4652826
  have hstable : (prefixWord ++ tailWord_4652826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4652826).length < 2 ^ (prefixWord ++ tailWord_4652826).sum := by decide
  have hdescent : baseEnd_4652826 < baseStart_4652826 := by decide
  rcases family_descends (prefixWord ++ tailWord_4652826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4652835 : List Nat := [1, 1, 1, 4, 2, 1, 2, 2, 1, 3, 5]
def baseStart_4652835 : Nat := 118140960795 + 4652835 * 2 ^ 59
def prefixEnd_4652835 : Nat := 4983230072969 + 3 ^ 40 * 4652835 * 2
def baseEnd_4652835 : Nat := 2389140761062408495364507

theorem tailTrace_4652835 : CollatzResearch.WordTrace tailWord_4652835 prefixEnd_4652835 2389140761062408495364507 := by
  unfold tailWord_4652835
  simp only [CollatzResearch.WordTrace]
  refine ⟨169702834098580910798511959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113135222732387273865674639 169702834098580910798511959)
  ·
    refine ⟨254554251147871366197767939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169702834098580910798511959 254554251147871366197767939)
    ·
      refine ⟨381831376721807049296651909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254554251147871366197767939 381831376721807049296651909)
      ·
        refine ⟨71593383135338821743122233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 381831376721807049296651909 71593383135338821743122233)
        ·
          refine ⟨53695037351504116307341675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71593383135338821743122233 53695037351504116307341675)
          ·
            refine ⟨80542556027256174461012513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53695037351504116307341675 80542556027256174461012513)
            ·
              refine ⟨60406917020442130845759385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80542556027256174461012513 60406917020442130845759385)
              ·
                refine ⟨45305187765331598134319539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60406917020442130845759385 45305187765331598134319539)
                ·
                  refine ⟨67957781647997397201479309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45305187765331598134319539 67957781647997397201479309)
                  ·
                    refine ⟨25484168117999023950554741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 67957781647997397201479309 25484168117999023950554741)
                    ·
                      refine ⟨2389140761062408495364507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25484168117999023950554741 2389140761062408495364507)
                      ·
                        rfl

theorem cell23_4652835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_4652835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4652835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4652835 prefixEnd_4652835 := by exact prefixLift 4652835
  have htrace : WordTrace (prefixWord ++ tailWord_4652835) baseStart_4652835 baseEnd_4652835 := by
    simpa [prefixWord, tailWord_4652835, baseEnd_4652835] using wordTrace_append hprefix tailTrace_4652835
  have hstable : (prefixWord ++ tailWord_4652835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4652835).length < 2 ^ (prefixWord ++ tailWord_4652835).sum := by decide
  have hdescent : baseEnd_4652835 < baseStart_4652835 := by decide
  rcases family_descends (prefixWord ++ tailWord_4652835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4652849 : List Nat := [1, 2, 2, 3, 2, 2, 1, 3, 1, 4, 2]
def baseStart_4652849 : Nat := 118140960795 + 4652849 * 2 ^ 59
def prefixEnd_4652849 : Nat := 4983230072969 + 3 ^ 40 * 4652849 * 2
def baseEnd_4652849 : Nat := 2389147949791571440589443

theorem tailTrace_4652849 : CollatzResearch.WordTrace tailWord_4652849 prefixEnd_4652849 2389147949791571440589443 := by
  unfold tailWord_4652849
  simp only [CollatzResearch.WordTrace]
  refine ⟨169703344720530191189521601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113135563147020127459681067 169703344720530191189521601)
  ·
    refine ⟨127277508540397643392141201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169703344720530191189521601 127277508540397643392141201)
    ·
      refine ⟨95458131405298232544105901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127277508540397643392141201 95458131405298232544105901)
      ·
        refine ⟨35796799276986837204039713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95458131405298232544105901 35796799276986837204039713)
        ·
          refine ⟨26847599457740127903029785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35796799276986837204039713 26847599457740127903029785)
          ·
            refine ⟨20135699593305095927272339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26847599457740127903029785 20135699593305095927272339)
            ·
              refine ⟨30203549389957643890908509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20135699593305095927272339 30203549389957643890908509)
              ·
                refine ⟨11326331021234116459090691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30203549389957643890908509 11326331021234116459090691)
                ·
                  refine ⟨16989496531851174688636037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11326331021234116459090691 16989496531851174688636037)
                  ·
                    refine ⟨3185530599722095254119257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16989496531851174688636037 3185530599722095254119257)
                    ·
                      refine ⟨2389147949791571440589443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3185530599722095254119257 2389147949791571440589443)
                      ·
                        rfl

theorem cell23_4652849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 3, 1, 4, 2].length) (baseStart_4652849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4652849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4652849 prefixEnd_4652849 := by exact prefixLift 4652849
  have htrace : WordTrace (prefixWord ++ tailWord_4652849) baseStart_4652849 baseEnd_4652849 := by
    simpa [prefixWord, tailWord_4652849, baseEnd_4652849] using wordTrace_append hprefix tailTrace_4652849
  have hstable : (prefixWord ++ tailWord_4652849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4652849).length < 2 ^ (prefixWord ++ tailWord_4652849).sum := by decide
  have hdescent : baseEnd_4652849 < baseStart_4652849 := by decide
  rcases family_descends (prefixWord ++ tailWord_4652849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4652870 : List Nat := [6, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2]
def baseStart_4652870 : Nat := 118140960795 + 4652870 * 2 ^ 59
def prefixEnd_4652870 : Nat := 4983230072969 + 3 ^ 40 * 4652870 * 2
def baseEnd_4652870 : Nat := 2389158732885315858426847

theorem tailTrace_4652870 : CollatzResearch.WordTrace tailWord_4652870 prefixEnd_4652870 2389158732885315858426847 := by
  unfold tailWord_4652870
  simp only [CollatzResearch.WordTrace]
  refine ⟨5303253457920440993001127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 113136073768969407850690709 5303253457920440993001127)
  ·
    refine ⟨7954880186880661489501691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5303253457920440993001127 7954880186880661489501691)
    ·
      refine ⟨11932320280320992234252537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7954880186880661489501691 11932320280320992234252537)
      ·
        refine ⟨8949240210240744175689403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11932320280320992234252537 8949240210240744175689403)
        ·
          refine ⟨13423860315361116263534105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8949240210240744175689403 13423860315361116263534105)
          ·
            refine ⟨10067895236520837197650579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13423860315361116263534105 10067895236520837197650579)
            ·
              refine ⟨15101842854781255796475869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10067895236520837197650579 15101842854781255796475869)
              ·
                refine ⟨5663191070542970923678451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15101842854781255796475869 5663191070542970923678451)
                ·
                  refine ⟨8494786605814456385517677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5663191070542970923678451 8494786605814456385517677)
                  ·
                    refine ⟨3185544977180421144569129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8494786605814456385517677 3185544977180421144569129)
                    ·
                      refine ⟨2389158732885315858426847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3185544977180421144569129 2389158732885315858426847)
                      ·
                        rfl

theorem cell23_4652870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_4652870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4652870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4652870 prefixEnd_4652870 := by exact prefixLift 4652870
  have htrace : WordTrace (prefixWord ++ tailWord_4652870) baseStart_4652870 baseEnd_4652870 := by
    simpa [prefixWord, tailWord_4652870, baseEnd_4652870] using wordTrace_append hprefix tailTrace_4652870
  have hstable : (prefixWord ++ tailWord_4652870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4652870).length < 2 ^ (prefixWord ++ tailWord_4652870).sum := by decide
  have hdescent : baseEnd_4652870 < baseStart_4652870 := by decide
  rcases family_descends (prefixWord ++ tailWord_4652870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4652900 : List Nat := [2, 3, 1, 1, 5, 1, 3, 1, 2, 2, 2]
def baseStart_4652900 : Nat := 118140960795 + 4652900 * 2 ^ 59
def prefixEnd_4652900 : Nat := 4983230072969 + 3 ^ 40 * 4652900 * 2
def baseEnd_4652900 : Nat := 2389174137304950741051709

theorem tailTrace_4652900 : CollatzResearch.WordTrace tailWord_4652900 prefixEnd_4652900 2389174137304950741051709 := by
  unfold tailWord_4652900
  simp only [CollatzResearch.WordTrace]
  refine ⟨84852602421672713449814077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113136803228896951266418769 84852602421672713449814077)
  ·
    refine ⟨31819725908127267543680279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84852602421672713449814077 31819725908127267543680279)
    ·
      refine ⟨47729588862190901315520419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31819725908127267543680279 47729588862190901315520419)
      ·
        refine ⟨71594383293286351973280629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47729588862190901315520419 71594383293286351973280629)
        ·
          refine ⟨6711973433745595497495059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 71594383293286351973280629 6711973433745595497495059)
          ·
            refine ⟨10067960150618393246242589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6711973433745595497495059 10067960150618393246242589)
            ·
              refine ⟨3775485056481897467340971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10067960150618393246242589 3775485056481897467340971)
              ·
                refine ⟨5663227584722846201011457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3775485056481897467340971 5663227584722846201011457)
                ·
                  refine ⟨4247420688542134650758593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5663227584722846201011457 4247420688542134650758593)
                  ·
                    refine ⟨3185565516406600988068945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4247420688542134650758593 3185565516406600988068945)
                    ·
                      refine ⟨2389174137304950741051709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3185565516406600988068945 2389174137304950741051709)
                      ·
                        rfl

theorem cell23_4652900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 3, 1, 2, 2, 2].length) (baseStart_4652900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4652900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4652900 prefixEnd_4652900 := by exact prefixLift 4652900
  have htrace : WordTrace (prefixWord ++ tailWord_4652900) baseStart_4652900 baseEnd_4652900 := by
    simpa [prefixWord, tailWord_4652900, baseEnd_4652900] using wordTrace_append hprefix tailTrace_4652900
  have hstable : (prefixWord ++ tailWord_4652900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4652900).length < 2 ^ (prefixWord ++ tailWord_4652900).sum := by decide
  have hdescent : baseEnd_4652900 < baseStart_4652900 := by decide
  rcases family_descends (prefixWord ++ tailWord_4652900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4652909 : List Nat := [1, 5, 1, 1, 1, 1, 2, 2, 2, 5, 2]
def baseStart_4652909 : Nat := 118140960795 + 4652909 * 2 ^ 59
def prefixEnd_4652909 : Nat := 4983230072969 + 3 ^ 40 * 4652909 * 2
def baseEnd_4652909 : Nat := 2389178758630841205839167

theorem tailTrace_4652909 : CollatzResearch.WordTrace tailWord_4652909 prefixEnd_4652909 2389178758630841205839167 := by
  unfold tailWord_4652909
  simp only [CollatzResearch.WordTrace]
  refine ⟨169705533100312821436705781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113137022066875214291137187 169705533100312821436705781)
  ·
    refine ⟨15909893728154327009691167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 169705533100312821436705781 15909893728154327009691167)
    ·
      refine ⟨23864840592231490514536751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15909893728154327009691167 23864840592231490514536751)
      ·
        refine ⟨35797260888347235771805127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23864840592231490514536751 35797260888347235771805127)
        ·
          refine ⟨53695891332520853657707691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35797260888347235771805127 53695891332520853657707691)
          ·
            refine ⟨80543836998781280486561537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53695891332520853657707691 80543836998781280486561537)
            ·
              refine ⟨60407877749085960364921153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80543836998781280486561537 60407877749085960364921153)
              ·
                refine ⟨45305908311814470273690865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60407877749085960364921153 45305908311814470273690865)
                ·
                  refine ⟨33979431233860852705268149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45305908311814470273690865 33979431233860852705268149)
                  ·
                    refine ⟨3185571678174454941118889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33979431233860852705268149 3185571678174454941118889)
                    ·
                      refine ⟨2389178758630841205839167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3185571678174454941118889 2389178758630841205839167)
                      ·
                        rfl

theorem cell23_4652909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 5, 2].length) (baseStart_4652909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4652909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4652909 prefixEnd_4652909 := by exact prefixLift 4652909
  have htrace : WordTrace (prefixWord ++ tailWord_4652909) baseStart_4652909 baseEnd_4652909 := by
    simpa [prefixWord, tailWord_4652909, baseEnd_4652909] using wordTrace_append hprefix tailTrace_4652909
  have hstable : (prefixWord ++ tailWord_4652909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4652909).length < 2 ^ (prefixWord ++ tailWord_4652909).sum := by decide
  have hdescent : baseEnd_4652909 < baseStart_4652909 := by decide
  rcases family_descends (prefixWord ++ tailWord_4652909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4652915 : List Nat := [1, 1, 1, 2, 2, 1, 3, 1, 1, 10]
def baseStart_4652915 : Nat := 118140960795 + 4652915 * 2 ^ 59
def prefixEnd_4652915 : Nat := 4983230072969 + 3 ^ 40 * 4652915 * 2
def baseEnd_4652915 : Nat := 796393946504922727454713

theorem tailTrace_4652915 : CollatzResearch.WordTrace tailWord_4652915 prefixEnd_4652915 796393946504922727454713 := by
  unfold tailWord_4652915
  simp only [CollatzResearch.WordTrace]
  refine ⟨169705751938291084461424199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113137167958860722974282799 169705751938291084461424199)
  ·
    refine ⟨254558627907436626692136299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169705751938291084461424199 254558627907436626692136299)
    ·
      refine ⟨381837941861154940038204449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254558627907436626692136299 381837941861154940038204449)
      ·
        refine ⟨286378456395866205028653337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 381837941861154940038204449 286378456395866205028653337)
        ·
          refine ⟨214783842296899653771490003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 286378456395866205028653337 214783842296899653771490003)
          ·
            refine ⟨322175763445349480657235005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214783842296899653771490003 322175763445349480657235005)
            ·
              refine ⟨120815911292006055246463127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 322175763445349480657235005 120815911292006055246463127)
              ·
                refine ⟨181223866938009082869694691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120815911292006055246463127 181223866938009082869694691)
                ·
                  refine ⟨271835800407013624304542037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 181223866938009082869694691 271835800407013624304542037)
                  ·
                    refine ⟨796393946504922727454713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 271835800407013624304542037 796393946504922727454713)
                    ·
                      rfl

theorem cell23_4652915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 10].length) (baseStart_4652915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4652915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4652915 prefixEnd_4652915 := by exact prefixLift 4652915
  have htrace : WordTrace (prefixWord ++ tailWord_4652915) baseStart_4652915 baseEnd_4652915 := by
    simpa [prefixWord, tailWord_4652915, baseEnd_4652915] using wordTrace_append hprefix tailTrace_4652915
  have hstable : (prefixWord ++ tailWord_4652915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4652915).length < 2 ^ (prefixWord ++ tailWord_4652915).sum := by decide
  have hdescent : baseEnd_4652915 < baseStart_4652915 := by decide
  rcases family_descends (prefixWord ++ tailWord_4652915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4652922 : List Nat := [3, 1, 1, 1, 1, 1, 6, 1, 1, 3, 4]
def baseStart_4652922 : Nat := 118140960795 + 4652922 * 2 ^ 59
def prefixEnd_4652922 : Nat := 4983230072969 + 3 ^ 40 * 4652922 * 2
def baseEnd_4652922 : Nat := 2389185433879349654976607

theorem tailTrace_4652922 : CollatzResearch.WordTrace tailWord_4652922 prefixEnd_4652922 2389185433879349654976607 := by
  unfold tailWord_4652922
  simp only [CollatzResearch.WordTrace]
  refine ⟨42426501812316431164232255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113137338166177149771286013 42426501812316431164232255)
  ·
    refine ⟨63639752718474646746348383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42426501812316431164232255 63639752718474646746348383)
    ·
      refine ⟨95459629077711970119522575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63639752718474646746348383 95459629077711970119522575)
      ·
        refine ⟨143189443616567955179283863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95459629077711970119522575 143189443616567955179283863)
        ·
          refine ⟨214784165424851932768925795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143189443616567955179283863 214784165424851932768925795)
          ·
            refine ⟨322176248137277899153388693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214784165424851932768925795 322176248137277899153388693)
            ·
              refine ⟨15102011631434901522815095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 322176248137277899153388693 15102011631434901522815095)
              ·
                refine ⟨22653017447152352284222643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15102011631434901522815095 22653017447152352284222643)
                ·
                  refine ⟨33979526170728528426333965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22653017447152352284222643 33979526170728528426333965)
                  ·
                    refine ⟨12742322314023198159875237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33979526170728528426333965 12742322314023198159875237)
                    ·
                      refine ⟨2389185433879349654976607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12742322314023198159875237 2389185433879349654976607)
                      ·
                        rfl

theorem cell23_4652922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 1, 3, 4].length) (baseStart_4652922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4652922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4652922 prefixEnd_4652922 := by exact prefixLift 4652922
  have htrace : WordTrace (prefixWord ++ tailWord_4652922) baseStart_4652922 baseEnd_4652922 := by
    simpa [prefixWord, tailWord_4652922, baseEnd_4652922] using wordTrace_append hprefix tailTrace_4652922
  have hstable : (prefixWord ++ tailWord_4652922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4652922).length < 2 ^ (prefixWord ++ tailWord_4652922).sum := by decide
  have hdescent : baseEnd_4652922 < baseStart_4652922 := by decide
  rcases family_descends (prefixWord ++ tailWord_4652922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4652999 : List Nat := [1, 1, 4, 1, 1, 2, 1, 2, 3, 5, 2]
def baseStart_4652999 : Nat := 118140960795 + 4652999 * 2 ^ 59
def prefixEnd_4652999 : Nat := 4983230072969 + 3 ^ 40 * 4652999 * 2
def baseEnd_4652999 : Nat := 2389224971889745853713753

theorem tailTrace_4652999 : CollatzResearch.WordTrace tailWord_4652999 prefixEnd_4652999 2389224971889745853713753 := by
  unfold tailWord_4652999
  simp only [CollatzResearch.WordTrace]
  refine ⟨169708815669986766807482051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113139210446657844538321367 169708815669986766807482051)
  ·
    refine ⟨254563223504980150211223077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169708815669986766807482051 254563223504980150211223077)
    ·
      refine ⟨47730604407183778164604327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 254563223504980150211223077 47730604407183778164604327)
      ·
        refine ⟨71595906610775667246906491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47730604407183778164604327 71595906610775667246906491)
        ·
          refine ⟨107393859916163500870359737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71595906610775667246906491 107393859916163500870359737)
          ·
            refine ⟨80545394937122625652769803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107393859916163500870359737 80545394937122625652769803)
            ·
              refine ⟨120818092405683938479154705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80545394937122625652769803 120818092405683938479154705)
              ·
                refine ⟨90613569304262953859366029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 120818092405683938479154705 90613569304262953859366029)
                ·
                  refine ⟨33980088489098607697262261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 90613569304262953859366029 33980088489098607697262261)
                  ·
                    refine ⟨3185633295852994471618337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33980088489098607697262261 3185633295852994471618337)
                    ·
                      refine ⟨2389224971889745853713753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3185633295852994471618337 2389224971889745853713753)
                      ·
                        rfl

theorem cell23_4652999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 5, 2].length) (baseStart_4652999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4652999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4652999 prefixEnd_4652999 := by exact prefixLift 4652999
  have htrace : WordTrace (prefixWord ++ tailWord_4652999) baseStart_4652999 baseEnd_4652999 := by
    simpa [prefixWord, tailWord_4652999, baseEnd_4652999] using wordTrace_append hprefix tailTrace_4652999
  have hstable : (prefixWord ++ tailWord_4652999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4652999).length < 2 ^ (prefixWord ++ tailWord_4652999).sum := by decide
  have hdescent : baseEnd_4652999 < baseStart_4652999 := by decide
  rcases family_descends (prefixWord ++ tailWord_4652999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4653000 : List Nat := [2, 1, 3, 1, 4, 3, 2, 2, 1, 4]
def baseStart_4653000 : Nat := 118140960795 + 4653000 * 2 ^ 59
def prefixEnd_4653000 : Nat := 4983230072969 + 3 ^ 40 * 4653000 * 2
def baseEnd_4653000 : Nat := 796408495123466783267083

theorem tailTrace_4653000 : CollatzResearch.WordTrace tailWord_4653000 prefixEnd_4653000 796408495123466783267083 := by
  unfold tailWord_4653000
  simp only [CollatzResearch.WordTrace]
  refine ⟨84854426071491571989134227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113139234761988762652178969 84854426071491571989134227)
  ·
    refine ⟨127281639107237357983701341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84854426071491571989134227 127281639107237357983701341)
    ·
      refine ⟨47730614665214009243888003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127281639107237357983701341 47730614665214009243888003)
      ·
        refine ⟨71595921997821013865832005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47730614665214009243888003 71595921997821013865832005)
        ·
          refine ⟨13424235374591440099843501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71595921997821013865832005 13424235374591440099843501)
          ·
            refine ⟨5034088265471790037441313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13424235374591440099843501 5034088265471790037441313)
            ·
              refine ⟨3775566199103842528080985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5034088265471790037441313 3775566199103842528080985)
              ·
                refine ⟨2831674649327881896060739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3775566199103842528080985 2831674649327881896060739)
                ·
                  refine ⟨4247511973991822844091109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2831674649327881896060739 4247511973991822844091109)
                  ·
                    refine ⟨796408495123466783267083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4247511973991822844091109 796408495123466783267083)
                    ·
                      rfl

theorem cell23_4653000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 2, 2, 1, 4].length) (baseStart_4653000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4653000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4653000 prefixEnd_4653000 := by exact prefixLift 4653000
  have htrace : WordTrace (prefixWord ++ tailWord_4653000) baseStart_4653000 baseEnd_4653000 := by
    simpa [prefixWord, tailWord_4653000, baseEnd_4653000] using wordTrace_append hprefix tailTrace_4653000
  have hstable : (prefixWord ++ tailWord_4653000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4653000).length < 2 ^ (prefixWord ++ tailWord_4653000).sum := by decide
  have hdescent : baseEnd_4653000 < baseStart_4653000 := by decide
  rcases family_descends (prefixWord ++ tailWord_4653000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4653006 : List Nat := [4, 1, 1, 1, 2, 2, 2, 3, 3, 1, 3]
def baseStart_4653006 : Nat := 118140960795 + 4653006 * 2 ^ 59
def prefixEnd_4653006 : Nat := 4983230072969 + 3 ^ 40 * 4653006 * 2
def baseEnd_4653006 : Nat := 2389228566254327326326221

theorem tailTrace_4653006 : CollatzResearch.WordTrace tailWord_4653006 prefixEnd_4653006 2389228566254327326326221 := by
  unfold tailWord_4653006
  simp only [CollatzResearch.WordTrace]
  refine ⟨21213633872620175875373359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113139380653974271335324581 21213633872620175875373359)
  ·
    refine ⟨31820450808930263813060039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21213633872620175875373359 31820450808930263813060039)
    ·
      refine ⟨47730676213395395719590059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31820450808930263813060039 47730676213395395719590059)
      ·
        refine ⟨71596014320093093579385089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47730676213395395719590059 71596014320093093579385089)
        ·
          refine ⟨53697010740069820184538817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71596014320093093579385089 53697010740069820184538817)
          ·
            refine ⟨40272758055052365138404113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53697010740069820184538817 40272758055052365138404113)
            ·
              refine ⟨30204568541289273853803085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40272758055052365138404113 30204568541289273853803085)
              ·
                refine ⟨11326713202983477695176157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30204568541289273853803085 11326713202983477695176157)
                ·
                  refine ⟨4247517451118804135691059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11326713202983477695176157 4247517451118804135691059)
                  ·
                    refine ⟨6371276176678206203536589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4247517451118804135691059 6371276176678206203536589)
                    ·
                      refine ⟨2389228566254327326326221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6371276176678206203536589 2389228566254327326326221)
                      ·
                        rfl

theorem cell23_4653006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 3, 3, 1, 3].length) (baseStart_4653006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4653006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4653006 prefixEnd_4653006 := by exact prefixLift 4653006
  have htrace : WordTrace (prefixWord ++ tailWord_4653006) baseStart_4653006 baseEnd_4653006 := by
    simpa [prefixWord, tailWord_4653006, baseEnd_4653006] using wordTrace_append hprefix tailTrace_4653006
  have hstable : (prefixWord ++ tailWord_4653006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4653006).length < 2 ^ (prefixWord ++ tailWord_4653006).sum := by decide
  have hdescent : baseEnd_4653006 < baseStart_4653006 := by decide
  rcases family_descends (prefixWord ++ tailWord_4653006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4653039 : List Nat := [1, 1, 2, 1, 4, 2, 2, 2, 4, 4]
def baseStart_4653039 : Nat := 118140960795 + 4653039 * 2 ^ 59
def prefixEnd_4653039 : Nat := 4983230072969 + 3 ^ 40 * 4653039 * 2
def baseEnd_4653039 : Nat := 796415170371975232404523

theorem tailTrace_4653039 : CollatzResearch.WordTrace tailWord_4653039 prefixEnd_4653039 796415170371975232404523 := by
  unfold tailWord_4653039
  simp only [CollatzResearch.WordTrace]
  refine ⟨169710274589841853638938171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113140183059894569092625447 169710274589841853638938171)
  ·
    refine ⟨254565411884762780458407257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169710274589841853638938171 254565411884762780458407257)
    ·
      refine ⟨190924058913572085343805443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 254565411884762780458407257 190924058913572085343805443)
      ·
        refine ⟨286386088370358128015708165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190924058913572085343805443 286386088370358128015708165)
        ·
          refine ⟨53697391569442149002945281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 286386088370358128015708165 53697391569442149002945281)
          ·
            refine ⟨40273043677081611752208961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53697391569442149002945281 40273043677081611752208961)
            ·
              refine ⟨30204782757811208814156721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40273043677081611752208961 30204782757811208814156721)
              ·
                refine ⟨22653587068358406610617541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30204782757811208814156721 22653587068358406610617541)
                ·
                  refine ⟨4247547575317201239490789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22653587068358406610617541 4247547575317201239490789)
                  ·
                    refine ⟨796415170371975232404523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4247547575317201239490789 796415170371975232404523)
                    ·
                      rfl

theorem cell23_4653039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 4, 4].length) (baseStart_4653039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4653039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4653039 prefixEnd_4653039 := by exact prefixLift 4653039
  have htrace : WordTrace (prefixWord ++ tailWord_4653039) baseStart_4653039 baseEnd_4653039 := by
    simpa [prefixWord, tailWord_4653039, baseEnd_4653039] using wordTrace_append hprefix tailTrace_4653039
  have hstable : (prefixWord ++ tailWord_4653039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4653039).length < 2 ^ (prefixWord ++ tailWord_4653039).sum := by decide
  have hdescent : baseEnd_4653039 < baseStart_4653039 := by decide
  rcases family_descends (prefixWord ++ tailWord_4653039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4653052 : List Nat := [2, 2, 2, 1, 2, 2, 12]
def baseStart_4653052 : Nat := 118140960795 + 4653052 * 2 ^ 59
def prefixEnd_4653052 : Nat := 4983230072969 + 3 ^ 40 * 4653052 * 2
def baseEnd_4653052 : Nat := 29496940572400421559889

theorem tailTrace_4653052 : CollatzResearch.WordTrace tailWord_4653052 prefixEnd_4653052 29496940572400421559889 := by
  unfold tailWord_4653052
  simp only [CollatzResearch.WordTrace]
  refine ⟨84855374369397378429580705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113140499159196504572774273 84855374369397378429580705)
  ·
    refine ⟨63641530777048033822185529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84855374369397378429580705 63641530777048033822185529)
    ·
      refine ⟨47731148082786025366639147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63641530777048033822185529 47731148082786025366639147)
      ·
        refine ⟨71596722124179038049958721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47731148082786025366639147 71596722124179038049958721)
        ·
          refine ⟨53697541593134278537469041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71596722124179038049958721 53697541593134278537469041)
          ·
            refine ⟨40273156194850708903101781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53697541593134278537469041 40273156194850708903101781)
            ·
              refine ⟨29496940572400421559889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 40273156194850708903101781 29496940572400421559889)
              ·
                rfl

theorem cell23_4653052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 12].length) (baseStart_4653052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4653052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4653052 prefixEnd_4653052 := by exact prefixLift 4653052
  have htrace : WordTrace (prefixWord ++ tailWord_4653052) baseStart_4653052 baseEnd_4653052 := by
    simpa [prefixWord, tailWord_4653052, baseEnd_4653052] using wordTrace_append hprefix tailTrace_4653052
  have hstable : (prefixWord ++ tailWord_4653052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4653052).length < 2 ^ (prefixWord ++ tailWord_4653052).sum := by decide
  have hdescent : baseEnd_4653052 < baseStart_4653052 := by decide
  rcases family_descends (prefixWord ++ tailWord_4653052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4653063 : List Nat := [1, 1, 4, 3, 1, 2, 1, 3, 3, 2, 2]
def baseStart_4653063 : Nat := 118140960795 + 4653063 * 2 ^ 59
def prefixEnd_4653063 : Nat := 4983230072969 + 3 ^ 40 * 4653063 * 2
def baseEnd_4653063 : Nat := 2389257834651633603313459

theorem tailTrace_4653063 : CollatzResearch.WordTrace tailWord_4653063 prefixEnd_4653063 2389257834651633603313459 := by
  unfold tailWord_4653063
  simp only [CollatzResearch.WordTrace]
  refine ⟨169711149941754905737811843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113140766627836603825207895 169711149941754905737811843)
  ·
    refine ⟨254566724912632358606717765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169711149941754905737811843 254566724912632358606717765)
    ·
      refine ⟨47731260921118567238759581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 254566724912632358606717765 47731260921118567238759581)
      ·
        refine ⟨17899222845419462714534843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47731260921118567238759581 17899222845419462714534843)
        ·
          refine ⟨26848834268129194071802265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17899222845419462714534843 26848834268129194071802265)
          ·
            refine ⟨20136625701096895553851699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26848834268129194071802265 20136625701096895553851699)
            ·
              refine ⟨30204938551645343330777549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20136625701096895553851699 30204938551645343330777549)
              ·
                refine ⟨11326851956867003749041581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30204938551645343330777549 11326851956867003749041581)
                ·
                  refine ⟨4247569483825126405890593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11326851956867003749041581 4247569483825126405890593)
                  ·
                    refine ⟨3185677112868844804417945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4247569483825126405890593 3185677112868844804417945)
                    ·
                      refine ⟨2389257834651633603313459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3185677112868844804417945 2389257834651633603313459)
                      ·
                        rfl

theorem cell23_4653063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 3, 3, 2, 2].length) (baseStart_4653063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4653063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4653063 prefixEnd_4653063 := by exact prefixLift 4653063
  have htrace : WordTrace (prefixWord ++ tailWord_4653063) baseStart_4653063 baseEnd_4653063 := by
    simpa [prefixWord, tailWord_4653063, baseEnd_4653063] using wordTrace_append hprefix tailTrace_4653063
  have hstable : (prefixWord ++ tailWord_4653063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4653063).length < 2 ^ (prefixWord ++ tailWord_4653063).sum := by decide
  have hdescent : baseEnd_4653063 < baseStart_4653063 := by decide
  rcases family_descends (prefixWord ++ tailWord_4653063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4653066 : List Nat := [3, 1, 2, 2, 4, 1, 1, 2, 1, 1, 5]
def baseStart_4653066 : Nat := 118140960795 + 4653066 * 2 ^ 59
def prefixEnd_4653066 : Nat := 4983230072969 + 3 ^ 40 * 4653066 * 2
def baseEnd_4653066 : Nat := 2389259375093597091575945

theorem tailTrace_4653066 : CollatzResearch.WordTrace tailWord_4653066 prefixEnd_4653066 2389259375093597091575945 := by
  unfold tailWord_4653066
  simp only [CollatzResearch.WordTrace]
  refine ⟨42427814840186009312542763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113140839573829358166780701 42427814840186009312542763)
  ·
    refine ⟨63641722260279013968814145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42427814840186009312542763 63641722260279013968814145)
    ·
      refine ⟨47731291695209260476610609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63641722260279013968814145 47731291695209260476610609)
      ·
        refine ⟨35798468771406945357457957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47731291695209260476610609 35798468771406945357457957)
        ·
          refine ⟨6712212894638802254523367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35798468771406945357457957 6712212894638802254523367)
          ·
            refine ⟨10068319341958203381785051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6712212894638802254523367 10068319341958203381785051)
            ·
              refine ⟨15102479012937305072677577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10068319341958203381785051 15102479012937305072677577)
              ·
                refine ⟨11326859259702978804508183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15102479012937305072677577 11326859259702978804508183)
                ·
                  refine ⟨16990288889554468206762275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11326859259702978804508183 16990288889554468206762275)
                  ·
                    refine ⟨25485433334331702310143413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16990288889554468206762275 25485433334331702310143413)
                    ·
                      refine ⟨2389259375093597091575945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25485433334331702310143413 2389259375093597091575945)
                      ·
                        rfl

theorem cell23_4653066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 2, 1, 1, 5].length) (baseStart_4653066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4653066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4653066 prefixEnd_4653066 := by exact prefixLift 4653066
  have htrace : WordTrace (prefixWord ++ tailWord_4653066) baseStart_4653066 baseEnd_4653066 := by
    simpa [prefixWord, tailWord_4653066, baseEnd_4653066] using wordTrace_append hprefix tailTrace_4653066
  have hstable : (prefixWord ++ tailWord_4653066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4653066).length < 2 ^ (prefixWord ++ tailWord_4653066).sum := by decide
  have hdescent : baseEnd_4653066 < baseStart_4653066 := by decide
  rcases family_descends (prefixWord ++ tailWord_4653066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4653072 : List Nat := [2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 6]
def baseStart_4653072 : Nat := 118140960795 + 4653072 * 2 ^ 59
def prefixEnd_4653072 : Nat := 4983230072969 + 3 ^ 40 * 4653072 * 2
def baseEnd_4653072 : Nat := 2389262455977524068100917

theorem tailTrace_4653072 : CollatzResearch.WordTrace tailWord_4653072 prefixEnd_4653072 2389262455977524068100917 := by
  unfold tailWord_4653072
  simp only [CollatzResearch.WordTrace]
  refine ⟨84855739099361150137444735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113140985465814866849926313 84855739099361150137444735)
  ·
    refine ⟨127283608649041725206167103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84855739099361150137444735 127283608649041725206167103)
    ·
      refine ⟨190925412973562587809250655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127283608649041725206167103 190925412973562587809250655)
      ·
        refine ⟨286388119460343881713875983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190925412973562587809250655 286388119460343881713875983)
        ·
          refine ⟨429582179190515822570813975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 286388119460343881713875983 429582179190515822570813975)
          ·
            refine ⟨644373268785773733856220963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 429582179190515822570813975 644373268785773733856220963)
            ·
              refine ⟨966559903178660600784331445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 644373268785773733856220963 966559903178660600784331445)
              ·
                refine ⟨90614990922999431323531073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 966559903178660600784331445 90614990922999431323531073)
                ·
                  refine ⟨67961243192249573492648305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90614990922999431323531073 67961243192249573492648305)
                  ·
                    refine ⟨50970932394187180119486229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 67961243192249573492648305 50970932394187180119486229)
                    ·
                      refine ⟨2389262455977524068100917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50970932394187180119486229 2389262455977524068100917)
                      ·
                        rfl

theorem cell23_4653072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 6].length) (baseStart_4653072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4653072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4653072 prefixEnd_4653072 := by exact prefixLift 4653072
  have htrace : WordTrace (prefixWord ++ tailWord_4653072) baseStart_4653072 baseEnd_4653072 := by
    simpa [prefixWord, tailWord_4653072, baseEnd_4653072] using wordTrace_append hprefix tailTrace_4653072
  have hstable : (prefixWord ++ tailWord_4653072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4653072).length < 2 ^ (prefixWord ++ tailWord_4653072).sum := by decide
  have hdescent : baseEnd_4653072 < baseStart_4653072 := by decide
  rcases family_descends (prefixWord ++ tailWord_4653072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4653166 : List Nat := [4, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4]
def baseStart_4653166 : Nat := 118140960795 + 4653166 * 2 ^ 59
def prefixEnd_4653166 : Nat := 4983230072969 + 3 ^ 40 * 4653166 * 2
def baseEnd_4653166 : Nat := 2389310723159046700325485

theorem tailTrace_4653166 : CollatzResearch.WordTrace tailWord_4653166 prefixEnd_4653166 2389310723159046700325485 := by
  unfold tailWord_4653166
  simp only [CollatzResearch.WordTrace]
  refine ⟨21214363332547719291101419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113143271106921169552540901 21214363332547719291101419)
  ·
    refine ⟨31821544998821578936652129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21214363332547719291101419 31821544998821578936652129)
    ·
      refine ⟨23866158749116184202489097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31821544998821578936652129 23866158749116184202489097)
      ·
        refine ⟨17899619061837138151866823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23866158749116184202489097 17899619061837138151866823)
        ·
          refine ⟨26849428592755707227800235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17899619061837138151866823 26849428592755707227800235)
          ·
            refine ⟨40274142889133560841700353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26849428592755707227800235 40274142889133560841700353)
            ·
              refine ⟨30205607166850170631275265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40274142889133560841700353 30205607166850170631275265)
              ·
                refine ⟨22654205375137627973456449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30205607166850170631275265 22654205375137627973456449)
                ·
                  refine ⟨16990654031353220980092337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22654205375137627973456449 16990654031353220980092337)
                  ·
                    refine ⟨12742990523514915735069253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16990654031353220980092337 12742990523514915735069253)
                    ·
                      refine ⟨2389310723159046700325485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12742990523514915735069253 2389310723159046700325485)
                      ·
                        rfl

theorem cell23_4653166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_4653166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4653166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4653166 prefixEnd_4653166 := by exact prefixLift 4653166
  have htrace : WordTrace (prefixWord ++ tailWord_4653166) baseStart_4653166 baseEnd_4653166 := by
    simpa [prefixWord, tailWord_4653166, baseEnd_4653166] using wordTrace_append hprefix tailTrace_4653166
  have hstable : (prefixWord ++ tailWord_4653166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4653166).length < 2 ^ (prefixWord ++ tailWord_4653166).sum := by decide
  have hdescent : baseEnd_4653166 < baseStart_4653166 := by decide
  rcases family_descends (prefixWord ++ tailWord_4653166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4653170 : List Nat := [3, 2, 1, 2, 2, 2, 1, 4, 2, 2, 2]
def baseStart_4653170 : Nat := 118140960795 + 4653170 * 2 ^ 59
def prefixEnd_4653170 : Nat := 4983230072969 + 3 ^ 40 * 4653170 * 2
def baseEnd_4653170 : Nat := 2389312777081664684675467

theorem tailTrace_4653170 : CollatzResearch.WordTrace tailWord_4653170 prefixEnd_4653170 2389312777081664684675467 := by
  unfold tailWord_4653170
  simp only [CollatzResearch.WordTrace]
  refine ⟨42428763138091815752989241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113143368368244842007971309 42428763138091815752989241)
  ·
    refine ⟨31821572353568861814741931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42428763138091815752989241 31821572353568861814741931)
    ·
      refine ⟨47732358530353292722112897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31821572353568861814741931 47732358530353292722112897)
      ·
        refine ⟨35799268897764969541584673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47732358530353292722112897 35799268897764969541584673)
        ·
          refine ⟨26849451673323727156188505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35799268897764969541584673 26849451673323727156188505)
          ·
            refine ⟨20137088754992795367141379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26849451673323727156188505 20137088754992795367141379)
            ·
              refine ⟨30205633132489193050712069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20137088754992795367141379 30205633132489193050712069)
              ·
                refine ⟨5663556212341723697008513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30205633132489193050712069 5663556212341723697008513)
                ·
                  refine ⟨4247667159256292772756385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5663556212341723697008513 4247667159256292772756385)
                  ·
                    refine ⟨3185750369442219579567289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4247667159256292772756385 3185750369442219579567289)
                    ·
                      refine ⟨2389312777081664684675467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3185750369442219579567289 2389312777081664684675467)
                      ·
                        rfl

theorem cell23_4653170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 4, 2, 2, 2].length) (baseStart_4653170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4653170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4653170 prefixEnd_4653170 := by exact prefixLift 4653170
  have htrace : WordTrace (prefixWord ++ tailWord_4653170) baseStart_4653170 baseEnd_4653170 := by
    simpa [prefixWord, tailWord_4653170, baseEnd_4653170] using wordTrace_append hprefix tailTrace_4653170
  have hstable : (prefixWord ++ tailWord_4653170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4653170).length < 2 ^ (prefixWord ++ tailWord_4653170).sum := by decide
  have hdescent : baseEnd_4653170 < baseStart_4653170 := by decide
  rcases family_descends (prefixWord ++ tailWord_4653170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4653210 : List Nat := [3, 1, 1, 5, 2, 1, 2, 3, 5]
def baseStart_4653210 : Nat := 118140960795 + 4653210 * 2 ^ 59
def prefixEnd_4653210 : Nat := 4983230072969 + 3 ^ 40 * 4653210 * 2
def baseEnd_4653210 : Nat := 265481479589760503130587

theorem tailTrace_4653210 : CollatzResearch.WordTrace tailWord_4653210 prefixEnd_4653210 265481479589760503130587 := by
  unfold tailWord_4653210
  simp only [CollatzResearch.WordTrace]
  refine ⟨42429127868055587460853271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113144340981481566562275389 42429127868055587460853271)
  ·
    refine ⟨63643691802083381191279907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42429127868055587460853271 63643691802083381191279907)
    ·
      refine ⟨95465537703125071786919861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63643691802083381191279907 95465537703125071786919861)
      ·
        refine ⟨8949894159667975480023737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 95465537703125071786919861 8949894159667975480023737)
        ·
          refine ⟨6712420619750981610017803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8949894159667975480023737 6712420619750981610017803)
          ·
            refine ⟨10068630929626472415026705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6712420619750981610017803 10068630929626472415026705)
            ·
              refine ⟨7551473197219854311270029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10068630929626472415026705 7551473197219854311270029)
              ·
                refine ⟨2831802448957445366726261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7551473197219854311270029 2831802448957445366726261)
                ·
                  refine ⟨265481479589760503130587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2831802448957445366726261 265481479589760503130587)
                  ·
                    rfl

theorem cell23_4653210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 3, 5].length) (baseStart_4653210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4653210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4653210 prefixEnd_4653210 := by exact prefixLift 4653210
  have htrace : WordTrace (prefixWord ++ tailWord_4653210) baseStart_4653210 baseEnd_4653210 := by
    simpa [prefixWord, tailWord_4653210, baseEnd_4653210] using wordTrace_append hprefix tailTrace_4653210
  have hstable : (prefixWord ++ tailWord_4653210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4653210).length < 2 ^ (prefixWord ++ tailWord_4653210).sum := by decide
  have hdescent : baseEnd_4653210 < baseStart_4653210 := by decide
  rcases family_descends (prefixWord ++ tailWord_4653210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4653266 : List Nat := [3, 2, 2, 2, 1, 2, 1, 2, 8]
def baseStart_4653266 : Nat := 118140960795 + 4653266 * 2 ^ 59
def prefixEnd_4653266 : Nat := 4983230072969 + 3 ^ 40 * 4653266 * 2
def baseEnd_4653266 : Nat := 265484674580499589897225

theorem tailTrace_4653266 : CollatzResearch.WordTrace tailWord_4653266 prefixEnd_4653266 265484674580499589897225 := by
  unfold tailWord_4653266
  simp only [CollatzResearch.WordTrace]
  refine ⟨42429638490004867851862913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113145702640012980938301101 42429638490004867851862913)
  ·
    refine ⟨31822228867503650888897185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42429638490004867851862913 31822228867503650888897185)
    ·
      refine ⟨23866671650627738166672889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31822228867503650888897185 23866671650627738166672889)
      ·
        refine ⟨17900003737970803625004667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23866671650627738166672889 17900003737970803625004667)
        ·
          refine ⟨26850005606956205437507001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17900003737970803625004667 26850005606956205437507001)
          ·
            refine ⟨20137504205217154078130251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26850005606956205437507001 20137504205217154078130251)
            ·
              refine ⟨30206256307825731117195377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20137504205217154078130251 30206256307825731117195377)
              ·
                refine ⟨22654692230869298337896533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30206256307825731117195377 22654692230869298337896533)
                ·
                  refine ⟨265484674580499589897225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22654692230869298337896533 265484674580499589897225)
                  ·
                    rfl

theorem cell23_4653266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 8].length) (baseStart_4653266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4653266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4653266 prefixEnd_4653266 := by exact prefixLift 4653266
  have htrace : WordTrace (prefixWord ++ tailWord_4653266) baseStart_4653266 baseEnd_4653266 := by
    simpa [prefixWord, tailWord_4653266, baseEnd_4653266] using wordTrace_append hprefix tailTrace_4653266
  have hstable : (prefixWord ++ tailWord_4653266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4653266).length < 2 ^ (prefixWord ++ tailWord_4653266).sum := by decide
  have hdescent : baseEnd_4653266 < baseStart_4653266 := by decide
  rcases family_descends (prefixWord ++ tailWord_4653266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4653310 : List Nat := [4, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3]
def baseStart_4653310 : Nat := 118140960795 + 4653310 * 2 ^ 59
def prefixEnd_4653310 : Nat := 4983230072969 + 3 ^ 40 * 4653310 * 2
def baseEnd_4653310 : Nat := 2389384664373294136924823

theorem tailTrace_4653310 : CollatzResearch.WordTrace tailWord_4653310 prefixEnd_4653310 2389384664373294136924823 := by
  unfold tailWord_4653310
  simp only [CollatzResearch.WordTrace]
  refine ⟨21215019846482508365256673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113146772514573377948035589 21215019846482508365256673)
  ·
    refine ⟨15911264884861881273942505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21215019846482508365256673 15911264884861881273942505)
    ·
      refine ⟨11933448663646410955456879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15911264884861881273942505 11933448663646410955456879)
      ·
        refine ⟨17900172995469616433185319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11933448663646410955456879 17900172995469616433185319)
        ·
          refine ⟨26850259493204424649777979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17900172995469616433185319 26850259493204424649777979)
          ·
            refine ⟨40275389239806636974666969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26850259493204424649777979 40275389239806636974666969)
            ·
              refine ⟨30206541929854977731000227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40275389239806636974666969 30206541929854977731000227)
              ·
                refine ⟨45309812894782466596500341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30206541929854977731000227 45309812894782466596500341)
                ·
                  refine ⟨4247794958885856243421907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45309812894782466596500341 4247794958885856243421907)
                  ·
                    refine ⟨6371692438328784365132861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4247794958885856243421907 6371692438328784365132861)
                    ·
                      refine ⟨2389384664373294136924823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6371692438328784365132861 2389384664373294136924823)
                      ·
                        rfl

theorem cell23_4653310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_4653310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4653310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4653310 prefixEnd_4653310 := by exact prefixLift 4653310
  have htrace : WordTrace (prefixWord ++ tailWord_4653310) baseStart_4653310 baseEnd_4653310 := by
    simpa [prefixWord, tailWord_4653310, baseEnd_4653310] using wordTrace_append hprefix tailTrace_4653310
  have hstable : (prefixWord ++ tailWord_4653310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4653310).length < 2 ^ (prefixWord ++ tailWord_4653310).sum := by decide
  have hdescent : baseEnd_4653310 < baseStart_4653310 := by decide
  rcases family_descends (prefixWord ++ tailWord_4653310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4653320 : List Nat := [2, 1, 3, 2, 3, 1, 1, 3, 2, 3, 2]
def baseStart_4653320 : Nat := 118140960795 + 4653320 * 2 ^ 59
def prefixEnd_4653320 : Nat := 4983230072969 + 3 ^ 40 * 4653320 * 2
def baseEnd_4653320 : Nat := 2389389799179839097799777

theorem tailTrace_4653320 : CollatzResearch.WordTrace tailWord_4653320 prefixEnd_4653320 2389389799179839097799777 := by
  unfold tailWord_4653320
  simp only [CollatzResearch.WordTrace]
  refine ⟨84860261750911919314958707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113147015667882559086611609 84860261750911919314958707)
  ·
    refine ⟨127290392626367878972438061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84860261750911919314958707 127290392626367878972438061)
    ·
      refine ⟨47733897234887954614664273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127290392626367878972438061 47733897234887954614664273)
      ·
        refine ⟨35800422926165965960998205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47733897234887954614664273 35800422926165965960998205)
        ·
          refine ⟨13425158597312237235374327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35800422926165965960998205 13425158597312237235374327)
          ·
            refine ⟨20137737895968355853061491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13425158597312237235374327 20137737895968355853061491)
            ·
              refine ⟨30206606843952533779592237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20137737895968355853061491 30206606843952533779592237)
              ·
                refine ⟨11327477566482200167347089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30206606843952533779592237 11327477566482200167347089)
                ·
                  refine ⟨8495608174861650125510317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11327477566482200167347089 8495608174861650125510317)
                  ·
                    refine ⟨3185853065573118797066369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8495608174861650125510317 3185853065573118797066369)
                    ·
                      refine ⟨2389389799179839097799777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3185853065573118797066369 2389389799179839097799777)
                      ·
                        rfl

theorem cell23_4653320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 3, 2, 3, 2].length) (baseStart_4653320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4653320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4653320 prefixEnd_4653320 := by exact prefixLift 4653320
  have htrace : WordTrace (prefixWord ++ tailWord_4653320) baseStart_4653320 baseEnd_4653320 := by
    simpa [prefixWord, tailWord_4653320, baseEnd_4653320] using wordTrace_append hprefix tailTrace_4653320
  have hstable : (prefixWord ++ tailWord_4653320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4653320).length < 2 ^ (prefixWord ++ tailWord_4653320).sum := by decide
  have hdescent : baseEnd_4653320 < baseStart_4653320 := by decide
  rcases family_descends (prefixWord ++ tailWord_4653320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4653333 : List Nat := [1, 3, 2, 1, 2, 1, 2, 5, 1, 1, 4]
def baseStart_4653333 : Nat := 118140960795 + 4653333 * 2 ^ 59
def prefixEnd_4653333 : Nat := 4983230072969 + 3 ^ 40 * 4653333 * 2
def baseEnd_4653333 : Nat := 2389396474428347546937217

theorem tailTrace_4653333 : CollatzResearch.WordTrace tailWord_4653333 prefixEnd_4653333 2389396474428347546937217 := by
  unfold tailWord_4653333
  simp only [CollatzResearch.WordTrace]
  refine ⟨169720997650776741850140653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113147331767184494566760435 169720997650776741850140653)
  ·
    refine ⟨63645374119041278193802745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169720997650776741850140653 63645374119041278193802745)
    ·
      refine ⟨47734030589280958645352059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63645374119041278193802745 47734030589280958645352059)
      ·
        refine ⟨71601045883921437968028089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47734030589280958645352059 71601045883921437968028089)
        ·
          refine ⟨53700784412941078476021067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71601045883921437968028089 53700784412941078476021067)
          ·
            refine ⟨80551176619411617714031601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53700784412941078476021067 80551176619411617714031601)
            ·
              refine ⟨60413382464558713285523701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80551176619411617714031601 60413382464558713285523701)
              ·
                refine ⟨5663754606052379370517847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 60413382464558713285523701 5663754606052379370517847)
                ·
                  refine ⟨8495631909078569055776771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5663754606052379370517847 8495631909078569055776771)
                  ·
                    refine ⟨12743447863617853583665157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8495631909078569055776771 12743447863617853583665157)
                    ·
                      refine ⟨2389396474428347546937217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12743447863617853583665157 2389396474428347546937217)
                      ·
                        rfl

theorem cell23_4653333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 5, 1, 1, 4].length) (baseStart_4653333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4653333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4653333 prefixEnd_4653333 := by exact prefixLift 4653333
  have htrace : WordTrace (prefixWord ++ tailWord_4653333) baseStart_4653333 baseEnd_4653333 := by
    simpa [prefixWord, tailWord_4653333, baseEnd_4653333] using wordTrace_append hprefix tailTrace_4653333
  have hstable : (prefixWord ++ tailWord_4653333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4653333).length < 2 ^ (prefixWord ++ tailWord_4653333).sum := by decide
  have hdescent : baseEnd_4653333 < baseStart_4653333 := by decide
  rcases family_descends (prefixWord ++ tailWord_4653333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4653344 : List Nat := [2, 1, 1, 5, 2, 1, 4, 2, 1, 1, 3]
def baseStart_4653344 : Nat := 118140960795 + 4653344 * 2 ^ 59
def prefixEnd_4653344 : Nat := 4983230072969 + 3 ^ 40 * 4653344 * 2
def baseEnd_4653344 : Nat := 2389402122715547003899667

theorem tailTrace_4653344 : CollatzResearch.WordTrace tailWord_4653344 prefixEnd_4653344 2389402122715547003899667 := by
  unfold tailWord_4653344
  simp only [CollatzResearch.WordTrace]
  refine ⟨84860699426868445364395543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113147599235824593819194057 84860699426868445364395543)
  ·
    refine ⟨127291049140302668046593315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84860699426868445364395543 127291049140302668046593315)
    ·
      refine ⟨190936573710454002069889973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127291049140302668046593315 190936573710454002069889973)
      ·
        refine ⟨17900303785355062694052185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 190936573710454002069889973 17900303785355062694052185)
        ·
          refine ⟨13425227839016297020539139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17900303785355062694052185 13425227839016297020539139)
          ·
            refine ⟨20137841758524445530808709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13425227839016297020539139 20137841758524445530808709)
            ·
              refine ⟨3775845329723333537026633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20137841758524445530808709 3775845329723333537026633)
              ·
                refine ⟨2831883997292500152769975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3775845329723333537026633 2831883997292500152769975)
                ·
                  refine ⟨4247825995938750229154963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2831883997292500152769975 4247825995938750229154963)
                  ·
                    refine ⟨6371738993908125343732445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4247825995938750229154963 6371738993908125343732445)
                    ·
                      refine ⟨2389402122715547003899667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6371738993908125343732445 2389402122715547003899667)
                      ·
                        rfl

theorem cell23_4653344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 4, 2, 1, 1, 3].length) (baseStart_4653344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4653344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4653344 prefixEnd_4653344 := by exact prefixLift 4653344
  have htrace : WordTrace (prefixWord ++ tailWord_4653344) baseStart_4653344 baseEnd_4653344 := by
    simpa [prefixWord, tailWord_4653344, baseEnd_4653344] using wordTrace_append hprefix tailTrace_4653344
  have hstable : (prefixWord ++ tailWord_4653344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4653344).length < 2 ^ (prefixWord ++ tailWord_4653344).sum := by decide
  have hdescent : baseEnd_4653344 < baseStart_4653344 := by decide
  rcases family_descends (prefixWord ++ tailWord_4653344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4653356 : List Nat := [2, 2, 1, 1, 1, 3, 5, 8]
def baseStart_4653356 : Nat := 118140960795 + 4653356 * 2 ^ 59
def prefixEnd_4653356 : Nat := 4983230072969 + 3 ^ 40 * 4653356 * 2
def baseEnd_4653356 : Nat := 88496603129014850257393

theorem tailTrace_4653356 : CollatzResearch.WordTrace tailWord_4653356 prefixEnd_4653356 88496603129014850257393 := by
  unfold tailWord_4653356
  simp only [CollatzResearch.WordTrace]
  refine ⟨84860918264846708389113961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113147891019795611185485281 84860918264846708389113961)
  ·
    refine ⟨63645688698635031291835471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84860918264846708389113961 63645688698635031291835471)
    ·
      refine ⟨95468533047952546937753207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63645688698635031291835471 95468533047952546937753207)
      ·
        refine ⟨143202799571928820406629811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95468533047952546937753207 143202799571928820406629811)
        ·
          refine ⟨214804199357893230609944717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143202799571928820406629811 214804199357893230609944717)
          ·
            refine ⟨80551574759209961478729269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 214804199357893230609944717 80551574759209961478729269)
            ·
              refine ⟨7551710133675933888630869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 80551574759209961478729269 7551710133675933888630869)
              ·
                refine ⟨88496603129014850257393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7551710133675933888630869 88496603129014850257393)
                ·
                  rfl

theorem cell23_4653356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 8].length) (baseStart_4653356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4653356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4653356 prefixEnd_4653356 := by exact prefixLift 4653356
  have htrace : WordTrace (prefixWord ++ tailWord_4653356) baseStart_4653356 baseEnd_4653356 := by
    simpa [prefixWord, tailWord_4653356, baseEnd_4653356] using wordTrace_append hprefix tailTrace_4653356
  have hstable : (prefixWord ++ tailWord_4653356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4653356).length < 2 ^ (prefixWord ++ tailWord_4653356).sum := by decide
  have hdescent : baseEnd_4653356 < baseStart_4653356 := by decide
  rcases family_descends (prefixWord ++ tailWord_4653356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4653363 : List Nat := [1, 1, 1, 2, 5, 1, 4, 1, 1, 2, 4]
def baseStart_4653363 : Nat := 118140960795 + 4653363 * 2 ^ 59
def prefixEnd_4653363 : Nat := 4983230072969 + 3 ^ 40 * 4653363 * 2
def baseEnd_4653363 : Nat := 2389411878847982429562079

theorem tailTrace_4653363 : CollatzResearch.WordTrace tailWord_4653363 prefixEnd_4653363 2389411878847982429562079 := by
  unfold tailWord_4653363
  simp only [CollatzResearch.WordTrace]
  refine ⟨169722091840668056973732743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113148061227112037982488495 169722091840668056973732743)
  ·
    refine ⟨254583137761002085460599115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169722091840668056973732743 254583137761002085460599115)
    ·
      refine ⟨381874706641503128190898673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254583137761002085460599115 381874706641503128190898673)
      ·
        refine ⟨286406029981127346143174005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 381874706641503128190898673 286406029981127346143174005)
        ·
          refine ⟨26850565310730688700922563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 286406029981127346143174005 26850565310730688700922563)
          ·
            refine ⟨40275847966096033051383845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26850565310730688700922563 40275847966096033051383845)
            ·
              refine ⟨7551721493643006197134471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40275847966096033051383845 7551721493643006197134471)
              ·
                refine ⟨11327582240464509295701707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7551721493643006197134471 11327582240464509295701707)
                ·
                  refine ⟨16991373360696763943552561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11327582240464509295701707 16991373360696763943552561)
                  ·
                    refine ⟨12743530020522572957664421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16991373360696763943552561 12743530020522572957664421)
                    ·
                      refine ⟨2389411878847982429562079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12743530020522572957664421 2389411878847982429562079)
                      ·
                        rfl

theorem cell23_4653363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 1, 1, 2, 4].length) (baseStart_4653363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4653363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4653363 prefixEnd_4653363 := by exact prefixLift 4653363
  have htrace : WordTrace (prefixWord ++ tailWord_4653363) baseStart_4653363 baseEnd_4653363 := by
    simpa [prefixWord, tailWord_4653363, baseEnd_4653363] using wordTrace_append hprefix tailTrace_4653363
  have hstable : (prefixWord ++ tailWord_4653363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4653363).length < 2 ^ (prefixWord ++ tailWord_4653363).sum := by decide
  have hdescent : baseEnd_4653363 < baseStart_4653363 := by decide
  rcases family_descends (prefixWord ++ tailWord_4653363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4653383 : List Nat := [1, 1, 4, 1, 2, 2, 1, 4, 1, 3, 3]
def baseStart_4653383 : Nat := 118140960795 + 4653383 * 2 ^ 59
def prefixEnd_4653383 : Nat := 4983230072969 + 3 ^ 40 * 4653383 * 2
def baseEnd_4653383 : Nat := 2389422148461072351311987

theorem tailTrace_4653383 : CollatzResearch.WordTrace tailWord_4653383 prefixEnd_4653383 2389422148461072351311987 := by
  unfold tailWord_4653383
  simp only [CollatzResearch.WordTrace]
  refine ⟨169722821300595600389460803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113148547533730400259640535 169722821300595600389460803)
  ·
    refine ⟨254584231950893400584191205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169722821300595600389460803 254584231950893400584191205)
    ·
      refine ⟨47734543490792512609535851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 254584231950893400584191205 47734543490792512609535851)
      ·
        refine ⟨71601815236188768914303777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47734543490792512609535851 71601815236188768914303777)
        ·
          refine ⟨53701361427141576685727833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71601815236188768914303777 53701361427141576685727833)
          ·
            refine ⟨40276021070356182514295875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53701361427141576685727833 40276021070356182514295875)
            ·
              refine ⟨60414031605534273771443813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40276021070356182514295875 60414031605534273771443813)
              ·
                refine ⟨11327630926037676332145715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60414031605534273771443813 11327630926037676332145715)
                ·
                  refine ⟨16991446389056514498218573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11327630926037676332145715 16991446389056514498218573)
                  ·
                    refine ⟨6371792395896192936831965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16991446389056514498218573 6371792395896192936831965)
                    ·
                      refine ⟨2389422148461072351311987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6371792395896192936831965 2389422148461072351311987)
                      ·
                        rfl

theorem cell23_4653383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 4, 1, 3, 3].length) (baseStart_4653383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4653383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4653383 prefixEnd_4653383 := by exact prefixLift 4653383
  have htrace : WordTrace (prefixWord ++ tailWord_4653383) baseStart_4653383 baseEnd_4653383 := by
    simpa [prefixWord, tailWord_4653383, baseEnd_4653383] using wordTrace_append hprefix tailTrace_4653383
  have hstable : (prefixWord ++ tailWord_4653383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4653383).length < 2 ^ (prefixWord ++ tailWord_4653383).sum := by decide
  have hdescent : baseEnd_4653383 < baseStart_4653383 := by decide
  rcases family_descends (prefixWord ++ tailWord_4653383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4653400 : List Nat := [2, 1, 2, 2, 1, 1, 2, 6, 2, 1, 3]
def baseStart_4653400 : Nat := 118140960795 + 4653400 * 2 ^ 59
def prefixEnd_4653400 : Nat := 4983230072969 + 3 ^ 40 * 4653400 * 2
def baseEnd_4653400 : Nat := 2389430877632198784799409

theorem tailTrace_4653400 : CollatzResearch.WordTrace tailWord_4653400 prefixEnd_4653400 2389430877632198784799409 := by
  unfold tailWord_4653400
  simp only [CollatzResearch.WordTrace]
  refine ⟨84861720670767006146414827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113148960894356008195219769 84861720670767006146414827)
  ·
    refine ⟨127292581006150509219622241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84861720670767006146414827 127292581006150509219622241)
    ·
      refine ⟨95469435754612881914716681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127292581006150509219622241 95469435754612881914716681)
      ·
        refine ⟨71602076815959661436037511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95469435754612881914716681 71602076815959661436037511)
        ·
          refine ⟨107403115223939492154056267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71602076815959661436037511 107403115223939492154056267)
          ·
            refine ⟨161104672835909238231084401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107403115223939492154056267 161104672835909238231084401)
            ·
              refine ⟨120828504626931928673313301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 161104672835909238231084401 120828504626931928673313301)
              ·
                refine ⟨5663836154387434156561561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 120828504626931928673313301 5663836154387434156561561)
                ·
                  refine ⟨4247877115790575617421171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5663836154387434156561561 4247877115790575617421171)
                  ·
                    refine ⟨6371815673685863426131757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4247877115790575617421171 6371815673685863426131757)
                    ·
                      refine ⟨2389430877632198784799409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6371815673685863426131757 2389430877632198784799409)
                      ·
                        rfl

theorem cell23_4653400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 6, 2, 1, 3].length) (baseStart_4653400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4653400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4653400 prefixEnd_4653400 := by exact prefixLift 4653400
  have htrace : WordTrace (prefixWord ++ tailWord_4653400) baseStart_4653400 baseEnd_4653400 := by
    simpa [prefixWord, tailWord_4653400, baseEnd_4653400] using wordTrace_append hprefix tailTrace_4653400
  have hstable : (prefixWord ++ tailWord_4653400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4653400).length < 2 ^ (prefixWord ++ tailWord_4653400).sum := by decide
  have hdescent : baseEnd_4653400 < baseStart_4653400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4653400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4653417 : List Nat := [1, 2, 1, 1, 1, 3, 7, 1, 2, 1, 3]
def baseStart_4653417 : Nat := 118140960795 + 4653417 * 2 ^ 59
def prefixEnd_4653417 : Nat := 4983230072969 + 3 ^ 40 * 4653417 * 2
def baseEnd_4653417 : Nat := 2389439606803325218286831

theorem tailTrace_4653417 : CollatzResearch.WordTrace tailWord_4653417 prefixEnd_4653417 2389439606803325218286831 := by
  unfold tailWord_4653417
  simp only [CollatzResearch.WordTrace]
  refine ⟨169724061382472424196198505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113149374254981616130799003 169724061382472424196198505)
  ·
    refine ⟨127293046036854318147148879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169724061382472424196198505 127293046036854318147148879)
    ·
      refine ⟨190939569055281477220723319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127293046036854318147148879 190939569055281477220723319)
      ·
        refine ⟨286409353582922215831084979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190939569055281477220723319 286409353582922215831084979)
        ·
          refine ⟨429614030374383323746627469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 286409353582922215831084979 429614030374383323746627469)
          ·
            refine ⟨161105261390393746404985301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 429614030374383323746627469 161105261390393746404985301)
            ·
              refine ⟨3775904563837353431366843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 161105261390393746404985301 3775904563837353431366843)
              ·
                refine ⟨5663856845756030147050265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3775904563837353431366843 5663856845756030147050265)
                ·
                  refine ⟨4247892634317022610287699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5663856845756030147050265 4247892634317022610287699)
                  ·
                    refine ⟨6371838951475533915431549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4247892634317022610287699 6371838951475533915431549)
                    ·
                      refine ⟨2389439606803325218286831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6371838951475533915431549 2389439606803325218286831)
                      ·
                        rfl

theorem cell23_4653417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 7, 1, 2, 1, 3].length) (baseStart_4653417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4653417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4653417 prefixEnd_4653417 := by exact prefixLift 4653417
  have htrace : WordTrace (prefixWord ++ tailWord_4653417) baseStart_4653417 baseEnd_4653417 := by
    simpa [prefixWord, tailWord_4653417, baseEnd_4653417] using wordTrace_append hprefix tailTrace_4653417
  have hstable : (prefixWord ++ tailWord_4653417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4653417).length < 2 ^ (prefixWord ++ tailWord_4653417).sum := by decide
  have hdescent : baseEnd_4653417 < baseStart_4653417 := by decide
  rcases family_descends (prefixWord ++ tailWord_4653417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4653463 : List Nat := [1, 1, 3, 3, 1, 1, 5, 1, 7]
def baseStart_4653463 : Nat := 118140960795 + 4653463 * 2 ^ 59
def prefixEnd_4653463 : Nat := 4983230072969 + 3 ^ 40 * 4653463 * 2
def baseEnd_4653463 : Nat := 265495914101492448701291

theorem tailTrace_4653463 : CollatzResearch.WordTrace tailWord_4653463 prefixEnd_4653463 265495914101492448701291 := by
  unfold tailWord_4653463
  simp only [CollatzResearch.WordTrace]
  refine ⟨169725739140305774052373043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113150492760203849368248695 169725739140305774052373043)
  ·
    refine ⟨254588608710458661078559565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169725739140305774052373043 254588608710458661078559565)
    ·
      refine ⟨95470728266421997904459837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 254588608710458661078559565 95470728266421997904459837)
      ·
        refine ⟨35801523099908249214172439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95470728266421997904459837 35801523099908249214172439)
        ·
          refine ⟨53702284649862373821258659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35801523099908249214172439 53702284649862373821258659)
          ·
            refine ⟨80553426974793560731887989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53702284649862373821258659 80553426974793560731887989)
            ·
              refine ⟨7551883778886896318614499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 80553426974793560731887989 7551883778886896318614499)
              ·
                refine ⟨11327825668330344477921749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7551883778886896318614499 11327825668330344477921749)
                ·
                  refine ⟨265495914101492448701291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11327825668330344477921749 265495914101492448701291)
                  ·
                    rfl

theorem cell23_4653463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 1, 7].length) (baseStart_4653463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4653463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4653463 prefixEnd_4653463 := by exact prefixLift 4653463
  have htrace : WordTrace (prefixWord ++ tailWord_4653463) baseStart_4653463 baseEnd_4653463 := by
    simpa [prefixWord, tailWord_4653463, baseEnd_4653463] using wordTrace_append hprefix tailTrace_4653463
  have hstable : (prefixWord ++ tailWord_4653463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4653463).length < 2 ^ (prefixWord ++ tailWord_4653463).sum := by decide
  have hdescent : baseEnd_4653463 < baseStart_4653463 := by decide
  rcases family_descends (prefixWord ++ tailWord_4653463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4653474 : List Nat := [3, 3, 1, 2, 1, 1, 3, 3, 2, 2, 2]
def baseStart_4653474 : Nat := 118140960795 + 4653474 * 2 ^ 59
def prefixEnd_4653474 : Nat := 4983230072969 + 3 ^ 40 * 4653474 * 2
def baseEnd_4653474 : Nat := 2389468875200631495274069

theorem tailTrace_4653474 : CollatzResearch.WordTrace tailWord_4653474 prefixEnd_4653474 2389468875200631495274069 := by
  unfold tailWord_4653474
  simp only [CollatzResearch.WordTrace]
  refine ⟨42431535085816480732755869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113150760228843948620682317 42431535085816480732755869)
  ·
    refine ⟨15911825657181180274783451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42431535085816480732755869 15911825657181180274783451)
    ·
      refine ⟨23867738485771770412175177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15911825657181180274783451 23867738485771770412175177)
      ·
        refine ⟨17900803864328827809131383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23867738485771770412175177 17900803864328827809131383)
        ·
          refine ⟨26851205796493241713697075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17900803864328827809131383 26851205796493241713697075)
          ·
            refine ⟨40276808694739862570545613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26851205796493241713697075 40276808694739862570545613)
            ·
              refine ⟨15103803260527448463954605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40276808694739862570545613 15103803260527448463954605)
              ·
                refine ⟨5663926222697793173982977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15103803260527448463954605 5663926222697793173982977)
                ·
                  refine ⟨4247944667023344880487233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5663926222697793173982977 4247944667023344880487233)
                  ·
                    refine ⟨3185958500267508660365425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4247944667023344880487233 3185958500267508660365425)
                    ·
                      refine ⟨2389468875200631495274069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3185958500267508660365425 2389468875200631495274069)
                      ·
                        rfl

theorem cell23_4653474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 3, 2, 2, 2].length) (baseStart_4653474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4653474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4653474 prefixEnd_4653474 := by exact prefixLift 4653474
  have htrace : WordTrace (prefixWord ++ tailWord_4653474) baseStart_4653474 baseEnd_4653474 := by
    simpa [prefixWord, tailWord_4653474, baseEnd_4653474] using wordTrace_append hprefix tailTrace_4653474
  have hstable : (prefixWord ++ tailWord_4653474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4653474).length < 2 ^ (prefixWord ++ tailWord_4653474).sum := by decide
  have hdescent : baseEnd_4653474 < baseStart_4653474 := by decide
  rcases family_descends (prefixWord ++ tailWord_4653474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4653553 : List Nat := [1, 2, 2, 2, 3, 1, 2, 2, 8]
def baseStart_4653553 : Nat := 118140960795 + 4653553 * 2 ^ 59
def prefixEnd_4653553 : Nat := 4983230072969 + 3 ^ 40 * 4653553 * 2
def baseEnd_4653553 : Nat := 265501048908037409576245

theorem tailTrace_4653553 : CollatzResearch.WordTrace tailWord_4653553 prefixEnd_4653553 265501048908037409576245 := by
  unfold tailWord_4653553
  simp only [CollatzResearch.WordTrace]
  refine ⟨169729021709979719423149313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113152681139986479615432875 169729021709979719423149313)
  ·
    refine ⟨127296766282484789567361985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169729021709979719423149313 127296766282484789567361985)
    ·
      refine ⟨95472574711863592175521489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127296766282484789567361985 95472574711863592175521489)
      ·
        refine ⟨71604431033897694131641117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95472574711863592175521489 71604431033897694131641117)
        ·
          refine ⟨26851661637711635299365419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71604431033897694131641117 26851661637711635299365419)
          ·
            refine ⟨40277492456567452949048129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26851661637711635299365419 40277492456567452949048129)
            ·
              refine ⟨30208119342425589711786097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40277492456567452949048129 30208119342425589711786097)
              ·
                refine ⟨22656089506819192283839573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30208119342425589711786097 22656089506819192283839573)
                ·
                  refine ⟨265501048908037409576245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22656089506819192283839573 265501048908037409576245)
                  ·
                    rfl

theorem cell23_4653553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 8].length) (baseStart_4653553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4653553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4653553 prefixEnd_4653553 := by exact prefixLift 4653553
  have htrace : WordTrace (prefixWord ++ tailWord_4653553) baseStart_4653553 baseEnd_4653553 := by
    simpa [prefixWord, tailWord_4653553, baseEnd_4653553] using wordTrace_append hprefix tailTrace_4653553
  have hstable : (prefixWord ++ tailWord_4653553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4653553).length < 2 ^ (prefixWord ++ tailWord_4653553).sum := by decide
  have hdescent : baseEnd_4653553 < baseStart_4653553 := by decide
  rcases family_descends (prefixWord ++ tailWord_4653553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4653573 : List Nat := [1, 3, 1, 1, 2, 2, 3, 1, 1, 2, 6]
def baseStart_4653573 : Nat := 118140960795 + 4653573 * 2 ^ 59
def prefixEnd_4653573 : Nat := 4983230072969 + 3 ^ 40 * 4653573 * 2
def baseEnd_4653573 : Nat := 2389519709785426607936113

theorem tailTrace_4653573 : CollatzResearch.WordTrace tailWord_4653573 prefixEnd_4653573 2389519709785426607936113 := by
  unfold tailWord_4653573
  simp only [CollatzResearch.WordTrace]
  refine ⟨169729751169907262838877373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113153167446604841892584915 169729751169907262838877373)
  ·
    refine ⟨63648656688715223564579015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169729751169907262838877373 63648656688715223564579015)
    ·
      refine ⟨95472985033072835346868523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63648656688715223564579015 95472985033072835346868523)
      ·
        refine ⟨143209477549609253020302785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95472985033072835346868523 143209477549609253020302785)
        ·
          refine ⟨107407108162206939765227089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143209477549609253020302785 107407108162206939765227089)
          ·
            refine ⟨80555331121655204823920317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107407108162206939765227089 80555331121655204823920317)
            ·
              refine ⟨30208249170620701808970119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80555331121655204823920317 30208249170620701808970119)
              ·
                refine ⟨45312373755931052713455179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30208249170620701808970119 45312373755931052713455179)
                ·
                  refine ⟨67968560633896579070182769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45312373755931052713455179 67968560633896579070182769)
                  ·
                    refine ⟨50976420475422434302637077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 67968560633896579070182769 50976420475422434302637077)
                    ·
                      refine ⟨2389519709785426607936113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50976420475422434302637077 2389519709785426607936113)
                      ·
                        rfl

theorem cell23_4653573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 2, 6].length) (baseStart_4653573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4653573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4653573 prefixEnd_4653573 := by exact prefixLift 4653573
  have htrace : WordTrace (prefixWord ++ tailWord_4653573) baseStart_4653573 baseEnd_4653573 := by
    simpa [prefixWord, tailWord_4653573, baseEnd_4653573] using wordTrace_append hprefix tailTrace_4653573
  have hstable : (prefixWord ++ tailWord_4653573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4653573).length < 2 ^ (prefixWord ++ tailWord_4653573).sum := by decide
  have hdescent : baseEnd_4653573 < baseStart_4653573 := by decide
  rcases family_descends (prefixWord ++ tailWord_4653573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4653581 : List Nat := [1, 7, 1, 1, 1, 1, 2, 1, 2, 4, 2]
def baseStart_4653581 : Nat := 118140960795 + 4653581 * 2 ^ 59
def prefixEnd_4653581 : Nat := 4983230072969 + 3 ^ 40 * 4653581 * 2
def baseEnd_4653581 : Nat := 2389523817630662576636077

theorem tailTrace_4653581 : CollatzResearch.WordTrace tailWord_4653581 prefixEnd_4653581 2389523817630662576636077 := by
  unfold tailWord_4653581
  simp only [CollatzResearch.WordTrace]
  refine ⟨169730042953878280205168597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113153361969252186803445731 169730042953878280205168597)
  ·
    refine ⟨3978047881731522192308639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 169730042953878280205168597 3978047881731522192308639)
    ·
      refine ⟨5967071822597283288462959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3978047881731522192308639 5967071822597283288462959)
      ·
        refine ⟨8950607733895924932694439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5967071822597283288462959 8950607733895924932694439)
        ·
          refine ⟨13425911600843887399041659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8950607733895924932694439 13425911600843887399041659)
          ·
            refine ⟨20138867401265831098562489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13425911600843887399041659 20138867401265831098562489)
            ·
              refine ⟨15104150550949373323921867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20138867401265831098562489 15104150550949373323921867)
              ·
                refine ⟨22656225826424059985882801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15104150550949373323921867 22656225826424059985882801)
                ·
                  refine ⟨16992169369818044989412101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22656225826424059985882801 16992169369818044989412101)
                  ·
                    refine ⟨3186031756840883435514769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16992169369818044989412101 3186031756840883435514769)
                    ·
                      refine ⟨2389523817630662576636077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3186031756840883435514769 2389523817630662576636077)
                      ·
                        rfl

theorem cell23_4653581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_4653581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4653581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4653581 prefixEnd_4653581 := by exact prefixLift 4653581
  have htrace : WordTrace (prefixWord ++ tailWord_4653581) baseStart_4653581 baseEnd_4653581 := by
    simpa [prefixWord, tailWord_4653581, baseEnd_4653581] using wordTrace_append hprefix tailTrace_4653581
  have hstable : (prefixWord ++ tailWord_4653581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4653581).length < 2 ^ (prefixWord ++ tailWord_4653581).sum := by decide
  have hdescent : baseEnd_4653581 < baseStart_4653581 := by decide
  rcases family_descends (prefixWord ++ tailWord_4653581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4653631 : List Nat := [1, 1, 2, 2, 3, 2, 5, 2, 1, 1, 3]
def baseStart_4653631 : Nat := 118140960795 + 4653631 * 2 ^ 59
def prefixEnd_4653631 : Nat := 4983230072969 + 3 ^ 40 * 4653631 * 2
def baseEnd_4653631 : Nat := 2389549491663387381010847

theorem tailTrace_4653631 : CollatzResearch.WordTrace tailWord_4653631 prefixEnd_4653631 2389549491663387381010847 := by
  unfold tailWord_4653631
  simp only [CollatzResearch.WordTrace]
  refine ⟨169731866603697138744488747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113154577735798092496325831 169731866603697138744488747)
  ·
    refine ⟨254597799905545708116733121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169731866603697138744488747 254597799905545708116733121)
    ·
      refine ⟨190948349929159281087549841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 254597799905545708116733121 190948349929159281087549841)
      ·
        refine ⟨143211262446869460815662381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190948349929159281087549841 143211262446869460815662381)
        ·
          refine ⟨53704223417576047805873393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 143211262446869460815662381 53704223417576047805873393)
          ·
            refine ⟨40278167563182035854405045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53704223417576047805873393 40278167563182035854405045)
            ·
              refine ⟨3776078209048315861350473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40278167563182035854405045 3776078209048315861350473)
              ·
                refine ⟨2832058656786236896012855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3776078209048315861350473 2832058656786236896012855)
                ·
                  refine ⟨4248087985179355344019283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2832058656786236896012855 4248087985179355344019283)
                  ·
                    refine ⟨6372131977769033016028925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4248087985179355344019283 6372131977769033016028925)
                    ·
                      refine ⟨2389549491663387381010847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6372131977769033016028925 2389549491663387381010847)
                      ·
                        rfl

theorem cell23_4653631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 5, 2, 1, 1, 3].length) (baseStart_4653631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4653631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4653631 prefixEnd_4653631 := by exact prefixLift 4653631
  have htrace : WordTrace (prefixWord ++ tailWord_4653631) baseStart_4653631 baseEnd_4653631 := by
    simpa [prefixWord, tailWord_4653631, baseEnd_4653631] using wordTrace_append hprefix tailTrace_4653631
  have hstable : (prefixWord ++ tailWord_4653631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4653631).length < 2 ^ (prefixWord ++ tailWord_4653631).sum := by decide
  have hdescent : baseEnd_4653631 < baseStart_4653631 := by decide
  rcases family_descends (prefixWord ++ tailWord_4653631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4653643 : List Nat := [1, 1, 1, 1, 3, 1, 5, 10]
def baseStart_4653643 : Nat := 118140960795 + 4653643 * 2 ^ 59
def prefixEnd_4653643 : Nat := 4983230072969 + 3 ^ 40 * 4653643 * 2
def baseEnd_4653643 : Nat := 88502061238194123483733

theorem tailTrace_4653643 : CollatzResearch.WordTrace tailWord_4653643 prefixEnd_4653643 88502061238194123483733 := by
  unfold tailWord_4653643
  simp only [CollatzResearch.WordTrace]
  refine ⟨169732304279653664793925583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113154869519769109862617055 169732304279653664793925583)
  ·
    refine ⟨254598456419480497190888375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169732304279653664793925583 254598456419480497190888375)
    ·
      refine ⟨381897684629220745786332563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254598456419480497190888375 381897684629220745786332563)
      ·
        refine ⟨572846526943831118679498845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 381897684629220745786332563 572846526943831118679498845)
        ·
          refine ⟨214817447603936669504812067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 572846526943831118679498845 214817447603936669504812067)
          ·
            refine ⟨322226171405905004257218101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214817447603936669504812067 322226171405905004257218101)
            ·
              refine ⟨30208703569303594149114197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 322226171405905004257218101 30208703569303594149114197)
              ·
                refine ⟨88502061238194123483733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 30208703569303594149114197 88502061238194123483733)
                ·
                  rfl

theorem cell23_4653643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 10].length) (baseStart_4653643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4653643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4653643 prefixEnd_4653643 := by exact prefixLift 4653643
  have htrace : WordTrace (prefixWord ++ tailWord_4653643) baseStart_4653643 baseEnd_4653643 := by
    simpa [prefixWord, tailWord_4653643, baseEnd_4653643] using wordTrace_append hprefix tailTrace_4653643
  have hstable : (prefixWord ++ tailWord_4653643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4653643).length < 2 ^ (prefixWord ++ tailWord_4653643).sum := by decide
  have hdescent : baseEnd_4653643 < baseStart_4653643 := by decide
  rcases family_descends (prefixWord ++ tailWord_4653643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4653650 : List Nat := [3, 2, 2, 1, 2, 1, 1, 3, 1, 1, 6]
def baseStart_4653650 : Nat := 118140960795 + 4653650 * 2 ^ 59
def prefixEnd_4653650 : Nat := 4983230072969 + 3 ^ 40 * 4653650 * 2
def baseEnd_4653650 : Nat := 2389559247795822806673259

theorem tailTrace_4653650 : CollatzResearch.WordTrace tailWord_4653650 prefixEnd_4653650 2389559247795822806673259 := by
  unfold tailWord_4653650
  simp only [CollatzResearch.WordTrace]
  refine ⟨42433139897657076247357601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113155039727085536659620269 42433139897657076247357601)
  ·
    refine ⟨31824854923242807185518201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42433139897657076247357601 31824854923242807185518201)
    ·
      refine ⟨23868641192432105389138651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31824854923242807185518201 23868641192432105389138651)
      ·
        refine ⟨35802961788648158083707977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23868641192432105389138651 35802961788648158083707977)
        ·
          refine ⟨26852221341486118562780983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35802961788648158083707977 26852221341486118562780983)
          ·
            refine ⟨40278332012229177844171475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26852221341486118562780983 40278332012229177844171475)
            ·
              refine ⟨60417498018343766766257213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40278332012229177844171475 60417498018343766766257213)
              ·
                refine ⟨22656561756878912537346455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60417498018343766766257213 22656561756878912537346455)
                ·
                  refine ⟨33984842635318368806019683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22656561756878912537346455 33984842635318368806019683)
                  ·
                    refine ⟨50977263952977553209029525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33984842635318368806019683 50977263952977553209029525)
                    ·
                      refine ⟨2389559247795822806673259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50977263952977553209029525 2389559247795822806673259)
                      ·
                        rfl

theorem cell23_4653650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_4653650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4653650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4653650 prefixEnd_4653650 := by exact prefixLift 4653650
  have htrace : WordTrace (prefixWord ++ tailWord_4653650) baseStart_4653650 baseEnd_4653650 := by
    simpa [prefixWord, tailWord_4653650, baseEnd_4653650] using wordTrace_append hprefix tailTrace_4653650
  have hstable : (prefixWord ++ tailWord_4653650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4653650).length < 2 ^ (prefixWord ++ tailWord_4653650).sum := by decide
  have hdescent : baseEnd_4653650 < baseStart_4653650 := by decide
  rcases family_descends (prefixWord ++ tailWord_4653650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4653671 : List Nat := [1, 1, 5, 1, 1, 1, 1, 7, 1, 2, 2]
def baseStart_4653671 : Nat := 118140960795 + 4653671 * 2 ^ 59
def prefixEnd_4653671 : Nat := 4983230072969 + 3 ^ 40 * 4653671 * 2
def baseEnd_4653671 : Nat := 2389570030889567224510663

theorem tailTrace_4653671 : CollatzResearch.WordTrace tailWord_4653671 prefixEnd_4653671 2389570030889567224510663 := by
  unfold tailWord_4653671
  simp only [CollatzResearch.WordTrace]
  refine ⟨169733325523552225575944867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113155550349034817050629911 169733325523552225575944867)
  ·
    refine ⟨254599988285328338363917301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169733325523552225575944867 254599988285328338363917301)
    ·
      refine ⟨23868748901749531721617247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 254599988285328338363917301 23868748901749531721617247)
      ·
        refine ⟨35803123352624297582425871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23868748901749531721617247 35803123352624297582425871)
        ·
          refine ⟨53704685028936446373638807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35803123352624297582425871 53704685028936446373638807)
          ·
            refine ⟨80557027543404669560458211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53704685028936446373638807 80557027543404669560458211)
            ·
              refine ⟨120835541315107004340687317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80557027543404669560458211 120835541315107004340687317)
              ·
                refine ⟨2832082999572820414234859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 120835541315107004340687317 2832082999572820414234859)
                ·
                  refine ⟨4248124499359230621352289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2832082999572820414234859 4248124499359230621352289)
                  ·
                    refine ⟨3186093374519422966014217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4248124499359230621352289 3186093374519422966014217)
                    ·
                      refine ⟨2389570030889567224510663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3186093374519422966014217 2389570030889567224510663)
                      ·
                        rfl

theorem cell23_4653671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 7, 1, 2, 2].length) (baseStart_4653671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4653671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4653671 prefixEnd_4653671 := by exact prefixLift 4653671
  have htrace : WordTrace (prefixWord ++ tailWord_4653671) baseStart_4653671 baseEnd_4653671 := by
    simpa [prefixWord, tailWord_4653671, baseEnd_4653671] using wordTrace_append hprefix tailTrace_4653671
  have hstable : (prefixWord ++ tailWord_4653671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4653671).length < 2 ^ (prefixWord ++ tailWord_4653671).sum := by decide
  have hdescent : baseEnd_4653671 < baseStart_4653671 := by decide
  rcases family_descends (prefixWord ++ tailWord_4653671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4653687 : List Nat := [1, 1, 3, 1, 1, 3, 2, 3, 4, 1, 3]
def baseStart_4653687 : Nat := 118140960795 + 4653687 * 2 ^ 59
def prefixEnd_4653687 : Nat := 4983230072969 + 3 ^ 40 * 4653687 * 2
def baseEnd_4653687 : Nat := 2389578246580039161910589

theorem tailTrace_4653687 : CollatzResearch.WordTrace tailWord_4653687 prefixEnd_4653687 2389578246580039161910589 := by
  unfold tailWord_4653687
  simp only [CollatzResearch.WordTrace]
  refine ⟨169733909091494260308527315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113155939394329506872351543 169733909091494260308527315)
  ·
    refine ⟨254600863637241390462790973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169733909091494260308527315 254600863637241390462790973)
    ·
      refine ⟨95475323863965521423546615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 254600863637241390462790973 95475323863965521423546615)
      ·
        refine ⟨143212985795948282135319923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95475323863965521423546615 143212985795948282135319923)
        ·
          refine ⟨214819478693922423202979885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143212985795948282135319923 214819478693922423202979885)
          ·
            refine ⟨80557304510220908701117457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 214819478693922423202979885 80557304510220908701117457)
            ·
              refine ⟨60417978382665681525838093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80557304510220908701117457 60417978382665681525838093)
              ·
                refine ⟨22656741893499630572189285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60417978382665681525838093 22656741893499630572189285)
                ·
                  refine ⟨4248139105031180732285491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22656741893499630572189285 4248139105031180732285491)
                  ·
                    refine ⟨6372208657546771098428237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4248139105031180732285491 6372208657546771098428237)
                    ·
                      refine ⟨2389578246580039161910589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6372208657546771098428237 2389578246580039161910589)
                      ·
                        rfl

theorem cell23_4653687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 4, 1, 3].length) (baseStart_4653687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4653687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4653687 prefixEnd_4653687 := by exact prefixLift 4653687
  have htrace : WordTrace (prefixWord ++ tailWord_4653687) baseStart_4653687 baseEnd_4653687 := by
    simpa [prefixWord, tailWord_4653687, baseEnd_4653687] using wordTrace_append hprefix tailTrace_4653687
  have hstable : (prefixWord ++ tailWord_4653687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4653687).length < 2 ^ (prefixWord ++ tailWord_4653687).sum := by decide
  have hdescent : baseEnd_4653687 < baseStart_4653687 := by decide
  rcases family_descends (prefixWord ++ tailWord_4653687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4653698 : List Nat := [3, 4, 3, 1, 1, 1, 2, 1, 1, 6]
def baseStart_4653698 : Nat := 118140960795 + 4653698 * 2 ^ 59
def prefixEnd_4653698 : Nat := 4983230072969 + 3 ^ 40 * 4653698 * 2
def baseEnd_4653698 : Nat := 796527964955746206291013

theorem tailTrace_4653698 : CollatzResearch.WordTrace tailWord_4653698 prefixEnd_4653698 796527964955746206291013 := by
  unfold tailWord_4653698
  simp only [CollatzResearch.WordTrace]
  refine ⟨42433577573613602296794437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113156206862969606124785165 42433577573613602296794437)
  ·
    refine ⟨7956295795052550430648957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42433577573613602296794437 7956295795052550430648957)
    ·
      refine ⟨2983610923144706411493359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7956295795052550430648957 2983610923144706411493359)
      ·
        refine ⟨4475416384717059617240039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2983610923144706411493359 4475416384717059617240039)
        ·
          refine ⟨6713124577075589425860059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4475416384717059617240039 6713124577075589425860059)
          ·
            refine ⟨10069686865613384138790089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6713124577075589425860059 10069686865613384138790089)
            ·
              refine ⟨7552265149210038104092567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10069686865613384138790089 7552265149210038104092567)
              ·
                refine ⟨11328397723815057156138851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7552265149210038104092567 11328397723815057156138851)
                ·
                  refine ⟨16992596585722585734208277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11328397723815057156138851 16992596585722585734208277)
                  ·
                    refine ⟨796527964955746206291013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16992596585722585734208277 796527964955746206291013)
                    ·
                      rfl

theorem cell23_4653698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_4653698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4653698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4653698 prefixEnd_4653698 := by exact prefixLift 4653698
  have htrace : WordTrace (prefixWord ++ tailWord_4653698) baseStart_4653698 baseEnd_4653698 := by
    simpa [prefixWord, tailWord_4653698, baseEnd_4653698] using wordTrace_append hprefix tailTrace_4653698
  have hstable : (prefixWord ++ tailWord_4653698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4653698).length < 2 ^ (prefixWord ++ tailWord_4653698).sum := by decide
  have hdescent : baseEnd_4653698 < baseStart_4653698 := by decide
  rcases family_descends (prefixWord ++ tailWord_4653698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4653720 : List Nat := [2, 1, 2, 4, 1, 1, 1, 2, 1, 8]
def baseStart_4653720 : Nat := 118140960795 + 4653720 * 2 ^ 59
def prefixEnd_4653720 : Nat := 4983230072969 + 3 ^ 40 * 4653720 * 2
def baseEnd_4653720 : Nat := 796531730480545844265979

theorem tailTrace_4653720 : CollatzResearch.WordTrace tailWord_4653720 prefixEnd_4653720 796531730480545844265979 := by
  unfold tailWord_4653720
  simp only [CollatzResearch.WordTrace]
  refine ⟨84867556350187353472239307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113156741800249804629652409 84867556350187353472239307)
  ·
    refine ⟨127301334525281030208358961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84867556350187353472239307 127301334525281030208358961)
    ·
      refine ⟨95476000893960772656269221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127301334525281030208358961 95476000893960772656269221)
      ·
        refine ⟨17901750167617644873050479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95476000893960772656269221 17901750167617644873050479)
        ·
          refine ⟨26852625251426467309575719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17901750167617644873050479 26852625251426467309575719)
          ·
            refine ⟨40278937877139700964363579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26852625251426467309575719 40278937877139700964363579)
            ·
              refine ⟨60418406815709551446545369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40278937877139700964363579 60418406815709551446545369)
              ·
                refine ⟨45313805111782163584909027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60418406815709551446545369 45313805111782163584909027)
                ·
                  refine ⟨67970707667673245377363541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45313805111782163584909027 67970707667673245377363541)
                  ·
                    refine ⟨796531730480545844265979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 67970707667673245377363541 796531730480545844265979)
                    ·
                      rfl

theorem cell23_4653720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 1, 8].length) (baseStart_4653720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4653720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4653720 prefixEnd_4653720 := by exact prefixLift 4653720
  have htrace : WordTrace (prefixWord ++ tailWord_4653720) baseStart_4653720 baseEnd_4653720 := by
    simpa [prefixWord, tailWord_4653720, baseEnd_4653720] using wordTrace_append hprefix tailTrace_4653720
  have hstable : (prefixWord ++ tailWord_4653720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4653720).length < 2 ^ (prefixWord ++ tailWord_4653720).sum := by decide
  have hdescent : baseEnd_4653720 < baseStart_4653720 := by decide
  rcases family_descends (prefixWord ++ tailWord_4653720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4653738 : List Nat := [3, 1, 5, 2, 1, 1, 1, 1, 4, 1, 3]
def baseStart_4653738 : Nat := 118140960795 + 4653738 * 2 ^ 59
def prefixEnd_4653738 : Nat := 4983230072969 + 3 ^ 40 * 4653738 * 2
def baseEnd_4653738 : Nat := 2389604434093418462372855

theorem tailTrace_4653738 : CollatzResearch.WordTrace tailWord_4653738 prefixEnd_4653738 2389604434093418462372855 := by
  unfold tailWord_4653738
  simp only [CollatzResearch.WordTrace]
  refine ⟨42433942303577374004658467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113157179476206330679089245 42433942303577374004658467)
  ·
    refine ⟨63650913455366061006987701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42433942303577374004658467 63650913455366061006987701)
    ·
      refine ⟨5967273136440568219405097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63650913455366061006987701 5967273136440568219405097)
      ·
        refine ⟨4475454852330426164553823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5967273136440568219405097 4475454852330426164553823)
        ·
          refine ⟨6713182278495639246830735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4475454852330426164553823 6713182278495639246830735)
          ·
            refine ⟨10069773417743458870246103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6713182278495639246830735 10069773417743458870246103)
            ·
              refine ⟨15104660126615188305369155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10069773417743458870246103 15104660126615188305369155)
              ·
                refine ⟨22656990189922782458053733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15104660126615188305369155 22656990189922782458053733)
                ·
                  refine ⟨4248185660610521710885075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22656990189922782458053733 4248185660610521710885075)
                  ·
                    refine ⟨6372278490915782566327613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4248185660610521710885075 6372278490915782566327613)
                    ·
                      refine ⟨2389604434093418462372855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6372278490915782566327613 2389604434093418462372855)
                      ·
                        rfl

theorem cell23_4653738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_4653738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4653738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4653738 prefixEnd_4653738 := by exact prefixLift 4653738
  have htrace : WordTrace (prefixWord ++ tailWord_4653738) baseStart_4653738 baseEnd_4653738 := by
    simpa [prefixWord, tailWord_4653738, baseEnd_4653738] using wordTrace_append hprefix tailTrace_4653738
  have hstable : (prefixWord ++ tailWord_4653738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4653738).length < 2 ^ (prefixWord ++ tailWord_4653738).sum := by decide
  have hdescent : baseEnd_4653738 < baseStart_4653738 := by decide
  rcases family_descends (prefixWord ++ tailWord_4653738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4653757 : List Nat := [1, 4, 1, 2, 1, 3, 2, 1, 2, 2, 4]
def baseStart_4653757 : Nat := 118140960795 + 4653757 * 2 ^ 59
def prefixEnd_4653757 : Nat := 4983230072969 + 3 ^ 40 * 4653757 * 2
def baseEnd_4653757 : Nat := 2389614190225853888035267

theorem tailTrace_4653757 : CollatzResearch.WordTrace tailWord_4653757 prefixEnd_4653757 2389614190225853888035267 := by
  unfold tailWord_4653757
  simp only [CollatzResearch.WordTrace]
  refine ⟨169736462201240662263575525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113157641467493774842383683 169736462201240662263575525)
  ·
    refine ⟨31825586662732624174420411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 169736462201240662263575525 31825586662732624174420411)
    ·
      refine ⟨47738379994098936261630617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31825586662732624174420411 47738379994098936261630617)
      ·
        refine ⟨35803784995574202196222963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47738379994098936261630617 35803784995574202196222963)
        ·
          refine ⟨53705677493361303294334445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35803784995574202196222963 53705677493361303294334445)
          ·
            refine ⟨20139629060010488735375417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53705677493361303294334445 20139629060010488735375417)
            ·
              refine ⟨15104721795007866551531563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20139629060010488735375417 15104721795007866551531563)
              ·
                refine ⟨22657082692511799827297345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15104721795007866551531563 22657082692511799827297345)
                ·
                  refine ⟨16992812019383849870473009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22657082692511799827297345 16992812019383849870473009)
                  ·
                    refine ⟨12744609014537887402854757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16992812019383849870473009 12744609014537887402854757)
                    ·
                      refine ⟨2389614190225853888035267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12744609014537887402854757 2389614190225853888035267)
                      ·
                        rfl

theorem cell23_4653757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_4653757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4653757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4653757 prefixEnd_4653757 := by exact prefixLift 4653757
  have htrace : WordTrace (prefixWord ++ tailWord_4653757) baseStart_4653757 baseEnd_4653757 := by
    simpa [prefixWord, tailWord_4653757, baseEnd_4653757] using wordTrace_append hprefix tailTrace_4653757
  have hstable : (prefixWord ++ tailWord_4653757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4653757).length < 2 ^ (prefixWord ++ tailWord_4653757).sum := by decide
  have hdescent : baseEnd_4653757 < baseStart_4653757 := by decide
  rcases family_descends (prefixWord ++ tailWord_4653757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4653784 : List Nat := [2, 1, 2, 2, 3, 2, 3, 3, 5]
def baseStart_4653784 : Nat := 118140960795 + 4653784 * 2 ^ 59
def prefixEnd_4653784 : Nat := 4983230072969 + 3 ^ 40 * 4653784 * 2
def baseEnd_4653784 : Nat := 265514228244836142488627

theorem tailTrace_4653784 : CollatzResearch.WordTrace tailWord_4653784 prefixEnd_4653784 265514228244836142488627 := by
  unfold tailWord_4653784
  simp only [CollatzResearch.WordTrace]
  refine ⟨84868723486071422937404203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113158297981428563916538937 84868723486071422937404203)
  ·
    refine ⟨127303085229107134406106305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84868723486071422937404203 127303085229107134406106305)
    ·
      refine ⟨95477313921830350804579729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127303085229107134406106305 95477313921830350804579729)
      ·
        refine ⟨71607985441372763103434797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95477313921830350804579729 71607985441372763103434797)
        ·
          refine ⟨26852994540514786163788049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71607985441372763103434797 26852994540514786163788049)
          ·
            refine ⟨20139745905386089622841037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26852994540514786163788049 20139745905386089622841037)
            ·
              refine ⟨7552404714519783608565389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20139745905386089622841037 7552404714519783608565389)
              ·
                refine ⟨2832151767944918853212021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7552404714519783608565389 2832151767944918853212021)
                ·
                  refine ⟨265514228244836142488627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2832151767944918853212021 265514228244836142488627)
                  ·
                    rfl

theorem cell23_4653784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 3, 5].length) (baseStart_4653784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4653784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4653784 prefixEnd_4653784 := by exact prefixLift 4653784
  have htrace : WordTrace (prefixWord ++ tailWord_4653784) baseStart_4653784 baseEnd_4653784 := by
    simpa [prefixWord, tailWord_4653784, baseEnd_4653784] using wordTrace_append hprefix tailTrace_4653784
  have hstable : (prefixWord ++ tailWord_4653784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4653784).length < 2 ^ (prefixWord ++ tailWord_4653784).sum := by decide
  have hdescent : baseEnd_4653784 < baseStart_4653784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4653784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4653787 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 6, 5, 2]
def baseStart_4653787 : Nat := 118140960795 + 4653787 * 2 ^ 59
def prefixEnd_4653787 : Nat := 4983230072969 + 3 ^ 40 * 4653787 * 2
def baseEnd_4653787 : Nat := 2389629594645488770660129

theorem tailTrace_4653787 : CollatzResearch.WordTrace tailWord_4653787 prefixEnd_4653787 2389629594645488770660129 := by
  unfold tailWord_4653787
  simp only [CollatzResearch.WordTrace]
  refine ⟨169737556391131977387167615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113158370927421318258111743 169737556391131977387167615)
  ·
    refine ⟨254606334586697966080751423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169737556391131977387167615 254606334586697966080751423)
    ·
      refine ⟨381909501880046949121127135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254606334586697966080751423 381909501880046949121127135)
      ·
        refine ⟨572864252820070423681690703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 381909501880046949121127135 572864252820070423681690703)
        ·
          refine ⟨859296379230105635522536055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 572864252820070423681690703 859296379230105635522536055)
          ·
            refine ⟨1288944568845158453283804083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 859296379230105635522536055 1288944568845158453283804083)
            ·
              refine ⟨1933416853267737679925706125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1288944568845158453283804083 1933416853267737679925706125)
              ·
                refine ⟨725031319975401629972139797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1933416853267737679925706125 725031319975401629972139797)
                ·
                  refine ⟨33985843123846951404944053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 725031319975401629972139797 33985843123846951404944053)
                  ·
                    refine ⟨3186172792860651694213505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33985843123846951404944053 3186172792860651694213505)
                    ·
                      refine ⟨2389629594645488770660129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3186172792860651694213505 2389629594645488770660129)
                      ·
                        rfl

theorem cell23_4653787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 5, 2].length) (baseStart_4653787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4653787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4653787 prefixEnd_4653787 := by exact prefixLift 4653787
  have htrace : WordTrace (prefixWord ++ tailWord_4653787) baseStart_4653787 baseEnd_4653787 := by
    simpa [prefixWord, tailWord_4653787, baseEnd_4653787] using wordTrace_append hprefix tailTrace_4653787
  have hstable : (prefixWord ++ tailWord_4653787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4653787).length < 2 ^ (prefixWord ++ tailWord_4653787).sum := by decide
  have hdescent : baseEnd_4653787 < baseStart_4653787 := by decide
  rcases family_descends (prefixWord ++ tailWord_4653787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4653797 : List Nat := [1, 3, 1, 4, 1, 2, 1, 1, 4, 5]
def baseStart_4653797 : Nat := 118140960795 + 4653797 * 2 ^ 59
def prefixEnd_4653797 : Nat := 4983230072969 + 3 ^ 40 * 4653797 * 2
def baseEnd_4653797 : Nat := 796544909817344577178361

theorem tailTrace_4653797 : CollatzResearch.WordTrace tailWord_4653797 prefixEnd_4653797 796544909817344577178361 := by
  unfold tailWord_4653797
  simp only [CollatzResearch.WordTrace]
  refine ⟨169737921121095749095031645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113158614080730499396687763 169737921121095749095031645)
  ·
    refine ⟨63651720420410905910636867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169737921121095749095031645 63651720420410905910636867)
    ·
      refine ⟨95477580630616358865955301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63651720420410905910636867 95477580630616358865955301)
      ·
        refine ⟨17902046368240567287366619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95477580630616358865955301 17902046368240567287366619)
        ·
          refine ⟨26853069552360850931049929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17902046368240567287366619 26853069552360850931049929)
          ·
            refine ⟨20139802164270638198287447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26853069552360850931049929 20139802164270638198287447)
            ·
              refine ⟨30209703246405957297431171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20139802164270638198287447 30209703246405957297431171)
              ·
                refine ⟨45314554869608935946146757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30209703246405957297431171 45314554869608935946146757)
                ·
                  refine ⟨8496479038051675489902517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45314554869608935946146757 8496479038051675489902517)
                  ·
                    refine ⟨796544909817344577178361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8496479038051675489902517 796544909817344577178361)
                    ·
                      rfl

theorem cell23_4653797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 4, 5].length) (baseStart_4653797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4653797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4653797 prefixEnd_4653797 := by exact prefixLift 4653797
  have htrace : WordTrace (prefixWord ++ tailWord_4653797) baseStart_4653797 baseEnd_4653797 := by
    simpa [prefixWord, tailWord_4653797, baseEnd_4653797] using wordTrace_append hprefix tailTrace_4653797
  have hstable : (prefixWord ++ tailWord_4653797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4653797).length < 2 ^ (prefixWord ++ tailWord_4653797).sum := by decide
  have hdescent : baseEnd_4653797 < baseStart_4653797 := by decide
  rcases family_descends (prefixWord ++ tailWord_4653797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4653807 : List Nat := [1, 1, 2, 1, 5, 3, 1, 1, 1, 2, 5]
def baseStart_4653807 : Nat := 118140960795 + 4653807 * 2 ^ 59
def prefixEnd_4653807 : Nat := 4983230072969 + 3 ^ 40 * 4653807 * 2
def baseEnd_4653807 : Nat := 2389639864258578692410037

theorem tailTrace_4653807 : CollatzResearch.WordTrace tailWord_4653807 prefixEnd_4653807 2389639864258578692410037 := by
  unfold tailWord_4653807
  simp only [CollatzResearch.WordTrace]
  refine ⟨169738285851059520802895675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113158857234039680535263783 169738285851059520802895675)
  ·
    refine ⟨254607428776589281204343513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169738285851059520802895675 254607428776589281204343513)
    ·
      refine ⟨190955571582441960903257635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 254607428776589281204343513 190955571582441960903257635)
      ·
        refine ⟨286433357373662941354886453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190955571582441960903257635 286433357373662941354886453)
        ·
          refine ⟨26853127253780900752020605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 286433357373662941354886453 26853127253780900752020605)
          ·
            refine ⟨10069922720167837782007727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26853127253780900752020605 10069922720167837782007727)
            ·
              refine ⟨15104884080251756673011591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10069922720167837782007727 15104884080251756673011591)
              ·
                refine ⟨22657326120377635009517387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15104884080251756673011591 22657326120377635009517387)
                ·
                  refine ⟨33985989180566452514276081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22657326120377635009517387 33985989180566452514276081)
                  ·
                    refine ⟨25489491885424839385707061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33985989180566452514276081 25489491885424839385707061)
                    ·
                      refine ⟨2389639864258578692410037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25489491885424839385707061 2389639864258578692410037)
                      ·
                        rfl

theorem cell23_4653807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 2, 5].length) (baseStart_4653807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4653807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4653807 prefixEnd_4653807 := by exact prefixLift 4653807
  have htrace : WordTrace (prefixWord ++ tailWord_4653807) baseStart_4653807 baseEnd_4653807 := by
    simpa [prefixWord, tailWord_4653807, baseEnd_4653807] using wordTrace_append hprefix tailTrace_4653807
  have hstable : (prefixWord ++ tailWord_4653807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4653807).length < 2 ^ (prefixWord ++ tailWord_4653807).sum := by decide
  have hdescent : baseEnd_4653807 < baseStart_4653807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4653807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4653812 : List Nat := [2, 6, 1, 1, 2, 1, 1, 3, 2, 2, 2]
def baseStart_4653812 : Nat := 118140960795 + 4653812 * 2 ^ 59
def prefixEnd_4653812 : Nat := 4983230072969 + 3 ^ 40 * 4653812 * 2
def baseEnd_4653812 : Nat := 2389642431661851172847515

theorem tailTrace_4653812 : CollatzResearch.WordTrace tailWord_4653812 prefixEnd_4653812 2389642431661851172847515 := by
  unfold tailWord_4653812
  simp only [CollatzResearch.WordTrace]
  refine ⟨84869234108020703328413845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113158978810694271104551793 84869234108020703328413845)
  ·
    refine ⟨3978245348813470468519399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 84869234108020703328413845 3978245348813470468519399)
    ·
      refine ⟨5967368023220205702779099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3978245348813470468519399 5967368023220205702779099)
      ·
        refine ⟨8951052034830308554168649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5967368023220205702779099 8951052034830308554168649)
        ·
          refine ⟨6713289026122731415626487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8951052034830308554168649 6713289026122731415626487)
          ·
            refine ⟨10069933539184097123439731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6713289026122731415626487 10069933539184097123439731)
            ·
              refine ⟨15104900308776145685159597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10069933539184097123439731 15104900308776145685159597)
              ·
                refine ⟨5664337615791054631934849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15104900308776145685159597 5664337615791054631934849)
                ·
                  refine ⟨4248253211843290973951137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5664337615791054631934849 4248253211843290973951137)
                  ·
                    refine ⟨3186189908882468230463353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4248253211843290973951137 3186189908882468230463353)
                    ·
                      refine ⟨2389642431661851172847515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3186189908882468230463353 2389642431661851172847515)
                      ·
                        rfl

theorem cell23_4653812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_4653812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4653812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4653812 prefixEnd_4653812 := by exact prefixLift 4653812
  have htrace : WordTrace (prefixWord ++ tailWord_4653812) baseStart_4653812 baseEnd_4653812 := by
    simpa [prefixWord, tailWord_4653812, baseEnd_4653812] using wordTrace_append hprefix tailTrace_4653812
  have hstable : (prefixWord ++ tailWord_4653812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4653812).length < 2 ^ (prefixWord ++ tailWord_4653812).sum := by decide
  have hdescent : baseEnd_4653812 < baseStart_4653812 := by decide
  rcases family_descends (prefixWord ++ tailWord_4653812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4653827 : List Nat := [1, 1, 1, 3, 2, 2, 1, 3, 5, 4]
def baseStart_4653827 : Nat := 118140960795 + 4653827 * 2 ^ 59
def prefixEnd_4653827 : Nat := 4983230072969 + 3 ^ 40 * 4653827 * 2
def baseEnd_4653827 : Nat := 796550044623889538053315

theorem tailTrace_4653827 : CollatzResearch.WordTrace tailWord_4653827 prefixEnd_4653827 796550044623889538053315 := by
  unfold tailWord_4653827
  simp only [CollatzResearch.WordTrace]
  refine ⟨169739015310987064218623735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113159343540658042812415823 169739015310987064218623735)
  ·
    refine ⟨254608522966480596327935603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169739015310987064218623735 254608522966480596327935603)
    ·
      refine ⟨381912784449720894491903405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254608522966480596327935603 381912784449720894491903405)
      ·
        refine ⟨143217294168645335434463777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 381912784449720894491903405 143217294168645335434463777)
        ·
          refine ⟨107412970626484001575847833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143217294168645335434463777 107412970626484001575847833)
          ·
            refine ⟨80559727969863001181885875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107412970626484001575847833 80559727969863001181885875)
            ·
              refine ⟨120839591954794501772828813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80559727969863001181885875 120839591954794501772828813)
              ·
                refine ⟨45314846983047938164810805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120839591954794501772828813 45314846983047938164810805)
                ·
                  refine ⟨4248266904660744202951013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45314846983047938164810805 4248266904660744202951013)
                  ·
                    refine ⟨796550044623889538053315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4248266904660744202951013 796550044623889538053315)
                    ·
                      rfl

theorem cell23_4653827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 5, 4].length) (baseStart_4653827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4653827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4653827 prefixEnd_4653827 := by exact prefixLift 4653827
  have htrace : WordTrace (prefixWord ++ tailWord_4653827) baseStart_4653827 baseEnd_4653827 := by
    simpa [prefixWord, tailWord_4653827, baseEnd_4653827] using wordTrace_append hprefix tailTrace_4653827
  have hstable : (prefixWord ++ tailWord_4653827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4653827).length < 2 ^ (prefixWord ++ tailWord_4653827).sum := by decide
  have hdescent : baseEnd_4653827 < baseStart_4653827 := by decide
  rcases family_descends (prefixWord ++ tailWord_4653827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4653834 : List Nat := [3, 1, 2, 2, 1, 2, 4, 1, 2, 1, 4]
def baseStart_4653834 : Nat := 118140960795 + 4653834 * 2 ^ 59
def prefixEnd_4653834 : Nat := 4983230072969 + 3 ^ 40 * 4653834 * 2
def baseEnd_4653834 : Nat := 2389653728236250086772413

theorem tailTrace_4653834 : CollatzResearch.WordTrace tailWord_4653834 prefixEnd_4653834 2389653728236250086772413 := by
  unfold tailWord_4653834
  simp only [CollatzResearch.WordTrace]
  refine ⟨42434817655490426103532139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113159513747974469609419037 42434817655490426103532139)
  ·
    refine ⟨63652226483235639155298209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42434817655490426103532139 63652226483235639155298209)
    ·
      refine ⟨47739169862426729366473657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63652226483235639155298209 47739169862426729366473657)
      ·
        refine ⟨35804377396820047024855243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47739169862426729366473657 35804377396820047024855243)
        ·
          refine ⟨53706566095230070537282865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35804377396820047024855243 53706566095230070537282865)
          ·
            refine ⟨40279924571422552902962149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53706566095230070537282865 40279924571422552902962149)
            ·
              refine ⟨7552485857141728669305403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40279924571422552902962149 7552485857141728669305403)
              ·
                refine ⟨11328728785712593003958105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7552485857141728669305403 11328728785712593003958105)
                ·
                  refine ⟨8496546589284444752968579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11328728785712593003958105 8496546589284444752968579)
                  ·
                    refine ⟨12744819883926667129452869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8496546589284444752968579 12744819883926667129452869)
                    ·
                      refine ⟨2389653728236250086772413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12744819883926667129452869 2389653728236250086772413)
                      ·
                        rfl

theorem cell23_4653834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 1, 2, 1, 4].length) (baseStart_4653834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4653834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4653834 prefixEnd_4653834 := by exact prefixLift 4653834
  have htrace : WordTrace (prefixWord ++ tailWord_4653834) baseStart_4653834 baseEnd_4653834 := by
    simpa [prefixWord, tailWord_4653834, baseEnd_4653834] using wordTrace_append hprefix tailTrace_4653834
  have hstable : (prefixWord ++ tailWord_4653834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4653834).length < 2 ^ (prefixWord ++ tailWord_4653834).sum := by decide
  have hdescent : baseEnd_4653834 < baseStart_4653834 := by decide
  rcases family_descends (prefixWord ++ tailWord_4653834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4653861 : List Nat := [1, 3, 1, 2, 3, 1, 3, 4, 1, 4]
def baseStart_4653861 : Nat := 118140960795 + 4653861 * 2 ^ 59
def prefixEnd_4653861 : Nat := 4983230072969 + 3 ^ 40 * 4653861 * 2
def baseEnd_4653861 : Nat := 796555864071307160378263

theorem tailTrace_4653861 : CollatzResearch.WordTrace tailWord_4653861 prefixEnd_4653861 796555864071307160378263 := by
  unfold tailWord_4653861
  simp only [CollatzResearch.WordTrace]
  refine ⟨169740255392863888025361437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113160170261909258683574291 169740255392863888025361437)
  ·
    refine ⟨63652595772323958009510539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169740255392863888025361437 63652595772323958009510539)
    ·
      refine ⟨95478893658485937014265809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63652595772323958009510539 95478893658485937014265809)
      ·
        refine ⟨71609170243864452760699357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95478893658485937014265809 71609170243864452760699357)
        ·
          refine ⟨26853438841449169785262259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71609170243864452760699357 26853438841449169785262259)
          ·
            refine ⟨40280158262173754677893389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26853438841449169785262259 40280158262173754677893389)
            ·
              refine ⟨15105059348315158004210021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40280158262173754677893389 15105059348315158004210021)
              ·
                refine ⟨2832198627809092125789379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15105059348315158004210021 2832198627809092125789379)
                ·
                  refine ⟨4248297941713638188684069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2832198627809092125789379 4248297941713638188684069)
                  ·
                    refine ⟨796555864071307160378263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4248297941713638188684069 796555864071307160378263)
                    ·
                      rfl

theorem cell23_4653861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 4, 1, 4].length) (baseStart_4653861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4653861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4653861 prefixEnd_4653861 := by exact prefixLift 4653861
  have htrace : WordTrace (prefixWord ++ tailWord_4653861) baseStart_4653861 baseEnd_4653861 := by
    simpa [prefixWord, tailWord_4653861, baseEnd_4653861] using wordTrace_append hprefix tailTrace_4653861
  have hstable : (prefixWord ++ tailWord_4653861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4653861).length < 2 ^ (prefixWord ++ tailWord_4653861).sum := by decide
  have hdescent : baseEnd_4653861 < baseStart_4653861 := by decide
  rcases family_descends (prefixWord ++ tailWord_4653861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4653878 : List Nat := [5, 1, 2, 2, 2, 1, 1, 2, 3, 4]
def baseStart_4653878 : Nat := 118140960795 + 4653878 * 2 ^ 59
def prefixEnd_4653878 : Nat := 4983230072969 + 3 ^ 40 * 4653878 * 2
def baseEnd_4653878 : Nat := 796558773795015971540737

theorem tailTrace_4653878 : CollatzResearch.WordTrace tailWord_4653878 prefixEnd_4653878 796558773795015971540737 := by
  unfold tailWord_4653878
  simp only [CollatzResearch.WordTrace]
  refine ⟨10608804714612643745545643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 113160583622534866619153525 10608804714612643745545643)
  ·
    refine ⟨15913207071918965618318465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10608804714612643745545643 15913207071918965618318465)
    ·
      refine ⟨11934905303939224213738849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15913207071918965618318465 11934905303939224213738849)
      ·
        refine ⟨8951178977954418160304137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11934905303939224213738849 8951178977954418160304137)
        ·
          refine ⟨6713384233465813620228103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8951178977954418160304137 6713384233465813620228103)
          ·
            refine ⟨10070076350198720430342155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6713384233465813620228103 10070076350198720430342155)
            ·
              refine ⟨15105114525298080645513233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10070076350198720430342155 15105114525298080645513233)
              ·
                refine ⟨11328835893973560484134925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15105114525298080645513233 11328835893973560484134925)
                ·
                  refine ⟨4248313460240085181550597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11328835893973560484134925 4248313460240085181550597)
                  ·
                    refine ⟨796558773795015971540737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4248313460240085181550597 796558773795015971540737)
                    ·
                      rfl

theorem cell23_4653878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_4653878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4653878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4653878 prefixEnd_4653878 := by exact prefixLift 4653878
  have htrace : WordTrace (prefixWord ++ tailWord_4653878) baseStart_4653878 baseEnd_4653878 := by
    simpa [prefixWord, tailWord_4653878, baseEnd_4653878] using wordTrace_append hprefix tailTrace_4653878
  have hstable : (prefixWord ++ tailWord_4653878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4653878).length < 2 ^ (prefixWord ++ tailWord_4653878).sum := by decide
  have hdescent : baseEnd_4653878 < baseStart_4653878 := by decide
  rcases family_descends (prefixWord ++ tailWord_4653878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4653908 : List Nat := [2, 4, 1, 1, 5, 1, 1, 2, 6]
def baseStart_4653908 : Nat := 118140960795 + 4653908 * 2 ^ 59
def prefixEnd_4653908 : Nat := 4983230072969 + 3 ^ 40 * 4653908 * 2
def baseEnd_4653908 : Nat := 265521302867186977471897

theorem tailTrace_4653908 : CollatzResearch.WordTrace tailWord_4653908 prefixEnd_4653908 265521302867186977471897 := by
  unfold tailWord_4653908
  simp only [CollatzResearch.WordTrace]
  refine ⟨84870984811846807526161189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113161313082462410034881585 84870984811846807526161189)
  ·
    refine ⟨15913309652221276411155223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84870984811846807526161189 15913309652221276411155223)
    ·
      refine ⟨23869964478331914616732835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15913309652221276411155223 23869964478331914616732835)
      ·
        refine ⟨35804946717497871925099253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23869964478331914616732835 35804946717497871925099253)
        ·
          refine ⟨3356713754765425492978055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35804946717497871925099253 3356713754765425492978055)
          ·
            refine ⟨5035070632148138239467083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3356713754765425492978055 5035070632148138239467083)
            ·
              refine ⟨7552605948222207359200625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5035070632148138239467083 7552605948222207359200625)
              ·
                refine ⟨5664454461166655519400469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7552605948222207359200625 5664454461166655519400469)
                ·
                  refine ⟨265521302867186977471897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5664454461166655519400469 265521302867186977471897)
                  ·
                    rfl

theorem cell23_4653908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 2, 6].length) (baseStart_4653908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4653908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4653908 prefixEnd_4653908 := by exact prefixLift 4653908
  have htrace : WordTrace (prefixWord ++ tailWord_4653908) baseStart_4653908 baseEnd_4653908 := by
    simpa [prefixWord, tailWord_4653908, baseEnd_4653908] using wordTrace_append hprefix tailTrace_4653908
  have hstable : (prefixWord ++ tailWord_4653908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4653908).length < 2 ^ (prefixWord ++ tailWord_4653908).sum := by decide
  have hdescent : baseEnd_4653908 < baseStart_4653908 := by decide
  rcases family_descends (prefixWord ++ tailWord_4653908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4653941 : List Nat := [1, 3, 4, 1, 1, 2, 1, 4, 1, 1, 4]
def baseStart_4653941 : Nat := 118140960795 + 4653941 * 2 ^ 59
def prefixEnd_4653941 : Nat := 4983230072969 + 3 ^ 40 * 4653941 * 2
def baseEnd_4653941 : Nat := 2389708670666281168134421

theorem tailTrace_4653941 : CollatzResearch.WordTrace tailWord_4653941 prefixEnd_4653941 2389708670666281168134421 := by
  unfold tailWord_4653941
  simp only [CollatzResearch.WordTrace]
  refine ⟨169743173232574061688273677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113162115488382707792182451 169743173232574061688273677)
  ·
    refine ⟨63653689962215273133102629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169743173232574061688273677 63653689962215273133102629)
    ·
      refine ⟨11935066867915363712456743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63653689962215273133102629 11935066867915363712456743)
      ·
        refine ⟨17902600301873045568685115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11935066867915363712456743 17902600301873045568685115)
        ·
          refine ⟨26853900452809568353027673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17902600301873045568685115 26853900452809568353027673)
          ·
            refine ⟨20140425339607176264770755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26853900452809568353027673 20140425339607176264770755)
            ·
              refine ⟨30210638009410764397156133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20140425339607176264770755 30210638009410764397156133)
              ·
                refine ⟨5664494626764518324466775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30210638009410764397156133 5664494626764518324466775)
                ·
                  refine ⟨8496741940146777486700163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5664494626764518324466775 8496741940146777486700163)
                  ·
                    refine ⟨12745112910220166230050245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8496741940146777486700163 12745112910220166230050245)
                    ·
                      refine ⟨2389708670666281168134421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12745112910220166230050245 2389708670666281168134421)
                      ·
                        rfl

theorem cell23_4653941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_4653941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4653941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4653941 prefixEnd_4653941 := by exact prefixLift 4653941
  have htrace : WordTrace (prefixWord ++ tailWord_4653941) baseStart_4653941 baseEnd_4653941 := by
    simpa [prefixWord, tailWord_4653941, baseEnd_4653941] using wordTrace_append hprefix tailTrace_4653941
  have hstable : (prefixWord ++ tailWord_4653941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4653941).length < 2 ^ (prefixWord ++ tailWord_4653941).sum := by decide
  have hdescent : baseEnd_4653941 < baseStart_4653941 := by decide
  rcases family_descends (prefixWord ++ tailWord_4653941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4653961 : List Nat := [1, 2, 1, 1, 5, 2, 2, 3, 1, 2, 3]
def baseStart_4653961 : Nat := 118140960795 + 4653961 * 2 ^ 59
def prefixEnd_4653961 : Nat := 4983230072969 + 3 ^ 40 * 4653961 * 2
def baseEnd_4653961 : Nat := 2389718940279371089884329

theorem tailTrace_4653961 : CollatzResearch.WordTrace tailWord_4653961 prefixEnd_4653961 2389718940279371089884329 := by
  unfold tailWord_4653961
  simp only [CollatzResearch.WordTrace]
  refine ⟨169743902692501605104001737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113162601795001070069334491 169743902692501605104001737)
  ·
    refine ⟨127307927019376203828001303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169743902692501605104001737 127307927019376203828001303)
    ·
      refine ⟨190961890529064305742001955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127307927019376203828001303 190961890529064305742001955)
      ·
        refine ⟨286442835793596458613002933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190961890529064305742001955 286442835793596458613002933)
        ·
          refine ⟨26854015855649667994969025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 286442835793596458613002933 26854015855649667994969025)
          ·
            refine ⟨20140511891737250996226769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26854015855649667994969025 20140511891737250996226769)
            ·
              refine ⟨15105383918802938247170077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20140511891737250996226769 15105383918802938247170077)
              ·
                refine ⟨5664518969551101842688779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15105383918802938247170077 5664518969551101842688779)
                ·
                  refine ⟨8496778454326652764033169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5664518969551101842688779 8496778454326652764033169)
                  ·
                    refine ⟨6372583840744989573024877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8496778454326652764033169 6372583840744989573024877)
                    ·
                      refine ⟨2389718940279371089884329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6372583840744989573024877 2389718940279371089884329)
                      ·
                        rfl

theorem cell23_4653961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 3, 1, 2, 3].length) (baseStart_4653961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4653961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4653961 prefixEnd_4653961 := by exact prefixLift 4653961
  have htrace : WordTrace (prefixWord ++ tailWord_4653961) baseStart_4653961 baseEnd_4653961 := by
    simpa [prefixWord, tailWord_4653961, baseEnd_4653961] using wordTrace_append hprefix tailTrace_4653961
  have hstable : (prefixWord ++ tailWord_4653961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4653961).length < 2 ^ (prefixWord ++ tailWord_4653961).sum := by decide
  have hdescent : baseEnd_4653961 < baseStart_4653961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4653961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4653977 : List Nat := [1, 2, 1, 2, 1, 3, 1, 3, 2, 7]
def baseStart_4653977 : Nat := 118140960795 + 4653977 * 2 ^ 59
def prefixEnd_4653977 : Nat := 4983230072969 + 3 ^ 40 * 4653977 * 2
def baseEnd_4653977 : Nat := 796575718656614342428085

theorem tailTrace_4653977 : CollatzResearch.WordTrace tailWord_4653977 prefixEnd_4653977 796575718656614342428085 := by
  unfold tailWord_4653977
  simp only [CollatzResearch.WordTrace]
  refine ⟨169744486260443639836584185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113162990840295759891056123 169744486260443639836584185)
  ·
    refine ⟨127308364695332729877438139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169744486260443639836584185 127308364695332729877438139)
    ·
      refine ⟨190962547042999094816157209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127308364695332729877438139 190962547042999094816157209)
      ·
        refine ⟨143221910282249321112117907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190962547042999094816157209 143221910282249321112117907)
        ·
          refine ⟨214832865423373981668176861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143221910282249321112117907 214832865423373981668176861)
          ·
            refine ⟨80562324533765243125566323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 214832865423373981668176861 80562324533765243125566323)
            ·
              refine ⟨120843486800647864688349485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80562324533765243125566323 120843486800647864688349485)
              ·
                refine ⟨45316307550242949258131057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120843486800647864688349485 45316307550242949258131057)
                ·
                  refine ⟨33987230662682211943598293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45316307550242949258131057 33987230662682211943598293)
                  ·
                    refine ⟨796575718656614342428085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33987230662682211943598293 796575718656614342428085)
                    ·
                      rfl

theorem cell23_4653977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 7].length) (baseStart_4653977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4653977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4653977 prefixEnd_4653977 := by exact prefixLift 4653977
  have htrace : WordTrace (prefixWord ++ tailWord_4653977) baseStart_4653977 baseEnd_4653977 := by
    simpa [prefixWord, tailWord_4653977, baseEnd_4653977] using wordTrace_append hprefix tailTrace_4653977
  have hstable : (prefixWord ++ tailWord_4653977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4653977).length < 2 ^ (prefixWord ++ tailWord_4653977).sum := by decide
  have hdescent : baseEnd_4653977 < baseStart_4653977 := by decide
  rcases family_descends (prefixWord ++ tailWord_4653977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4653985 : List Nat := [1, 2, 3, 4, 1, 3, 2, 1, 2, 4]
def baseStart_4653985 : Nat := 118140960795 + 4653985 * 2 ^ 59
def prefixEnd_4653985 : Nat := 4983230072969 + 3 ^ 40 * 4653985 * 2
def baseEnd_4653985 : Nat := 796577087938359665328073

theorem tailTrace_4653985 : CollatzResearch.WordTrace tailWord_4653985 prefixEnd_4653985 796577087938359665328073 := by
  unfold tailWord_4653985
  simp only [CollatzResearch.WordTrace]
  refine ⟨169744778044414657202875409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113163185362943104801916939 169744778044414657202875409)
  ·
    refine ⟨127308583533310992902156557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169744778044414657202875409 127308583533310992902156557)
    ·
      refine ⟨47740718824991622338308709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127308583533310992902156557 47740718824991622338308709)
      ·
        refine ⟨8951384779685929188432883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47740718824991622338308709 8951384779685929188432883)
        ·
          refine ⟨13427077169528893782649325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8951384779685929188432883 13427077169528893782649325)
          ·
            refine ⟨5035153938573335168493497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13427077169528893782649325 5035153938573335168493497)
            ·
              refine ⟨3776365453930001376370123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5035153938573335168493497 3776365453930001376370123)
              ·
                refine ⟨5664548180895002064555185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3776365453930001376370123 5664548180895002064555185)
                ·
                  refine ⟨4248411135671251548416389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5664548180895002064555185 4248411135671251548416389)
                  ·
                    refine ⟨796577087938359665328073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4248411135671251548416389 796577087938359665328073)
                    ·
                      rfl

theorem cell23_4653985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 2, 1, 2, 4].length) (baseStart_4653985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4653985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4653985 prefixEnd_4653985 := by exact prefixLift 4653985
  have htrace : WordTrace (prefixWord ++ tailWord_4653985) baseStart_4653985 baseEnd_4653985 := by
    simpa [prefixWord, tailWord_4653985, baseEnd_4653985] using wordTrace_append hprefix tailTrace_4653985
  have hstable : (prefixWord ++ tailWord_4653985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4653985).length < 2 ^ (prefixWord ++ tailWord_4653985).sum := by decide
  have hdescent : baseEnd_4653985 < baseStart_4653985 := by decide
  rcases family_descends (prefixWord ++ tailWord_4653985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4654064 : List Nat := [2, 1, 1, 1, 3, 2, 1, 1, 3, 5, 3]
def baseStart_4654064 : Nat := 118140960795 + 4654064 * 2 ^ 59
def prefixEnd_4654064 : Nat := 4983230072969 + 3 ^ 40 * 4654064 * 2
def baseEnd_4654064 : Nat := 2389771828786784186896355

theorem tailTrace_4654064 : CollatzResearch.WordTrace tailWord_4654064 prefixEnd_4654064 2389771828786784186896355 := by
  unfold tailWord_4654064
  simp only [CollatzResearch.WordTrace]
  refine ⟨84873829705564226847500623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113165106274085635796667497 84873829705564226847500623)
  ·
    refine ⟨127310744558346340271250935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84873829705564226847500623 127310744558346340271250935)
    ·
      refine ⟨190966116837519510406876403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127310744558346340271250935 190966116837519510406876403)
      ·
        refine ⟨286449175256279265610314605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190966116837519510406876403 286449175256279265610314605)
        ·
          refine ⟨107418440721104724603867977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 286449175256279265610314605 107418440721104724603867977)
          ·
            refine ⟨80563830540828543452900983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107418440721104724603867977 80563830540828543452900983)
            ·
              refine ⟨120845745811242815179351475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80563830540828543452900983 120845745811242815179351475)
              ·
                refine ⟨181268618716864222769027213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120845745811242815179351475 181268618716864222769027213)
                ·
                  refine ⟨67975732018824083538385205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 181268618716864222769027213 67975732018824083538385205)
                  ·
                    refine ⟨6372724876764757831723613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 67975732018824083538385205 6372724876764757831723613)
                    ·
                      refine ⟨2389771828786784186896355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6372724876764757831723613 2389771828786784186896355)
                      ·
                        rfl

theorem cell23_4654064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 3, 5, 3].length) (baseStart_4654064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4654064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4654064 prefixEnd_4654064 := by exact prefixLift 4654064
  have htrace : WordTrace (prefixWord ++ tailWord_4654064) baseStart_4654064 baseEnd_4654064 := by
    simpa [prefixWord, tailWord_4654064, baseEnd_4654064] using wordTrace_append hprefix tailTrace_4654064
  have hstable : (prefixWord ++ tailWord_4654064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4654064).length < 2 ^ (prefixWord ++ tailWord_4654064).sum := by decide
  have hdescent : baseEnd_4654064 < baseStart_4654064 := by decide
  rcases family_descends (prefixWord ++ tailWord_4654064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4654081 : List Nat := [1, 2, 4, 1, 2, 2, 1, 2, 2, 3, 3]
def baseStart_4654081 : Nat := 118140960795 + 4654081 * 2 ^ 59
def prefixEnd_4654081 : Nat := 4983230072969 + 3 ^ 40 * 4654081 * 2
def baseEnd_4654081 : Nat := 2389780557957910620383777

theorem tailTrace_4654081 : CollatzResearch.WordTrace tailWord_4654081 prefixEnd_4654081 2389780557957910620383777 := by
  unfold tailWord_4654081
  simp only [CollatzResearch.WordTrace]
  refine ⟨169748279452066865598370097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113165519634711243732246731 169748279452066865598370097)
  ·
    refine ⟨127311209589050149198777573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169748279452066865598370097 127311209589050149198777573)
    ·
      refine ⟨23870851797946902974770795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127311209589050149198777573 23870851797946902974770795)
      ·
        refine ⟨35806277696920354462156193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23870851797946902974770795 35806277696920354462156193)
        ·
          refine ⟨26854708272690265846617145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35806277696920354462156193 26854708272690265846617145)
          ·
            refine ⟨20141031204517699384962859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26854708272690265846617145 20141031204517699384962859)
            ·
              refine ⟨30211546806776549077444289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20141031204517699384962859 30211546806776549077444289)
              ·
                refine ⟨22658660105082411808083217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30211546806776549077444289 22658660105082411808083217)
                ·
                  refine ⟨16993995078811808856062413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22658660105082411808083217 16993995078811808856062413)
                  ·
                    refine ⟨6372748154554428321023405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16993995078811808856062413 6372748154554428321023405)
                    ·
                      refine ⟨2389780557957910620383777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6372748154554428321023405 2389780557957910620383777)
                      ·
                        rfl

theorem cell23_4654081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 2, 3, 3].length) (baseStart_4654081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4654081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4654081 prefixEnd_4654081 := by exact prefixLift 4654081
  have htrace : WordTrace (prefixWord ++ tailWord_4654081) baseStart_4654081 baseEnd_4654081 := by
    simpa [prefixWord, tailWord_4654081, baseEnd_4654081] using wordTrace_append hprefix tailTrace_4654081
  have hstable : (prefixWord ++ tailWord_4654081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4654081).length < 2 ^ (prefixWord ++ tailWord_4654081).sum := by decide
  have hdescent : baseEnd_4654081 < baseStart_4654081 := by decide
  rcases family_descends (prefixWord ++ tailWord_4654081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4654122 : List Nat := [3, 1, 4, 1, 4, 1, 1, 3, 5]
def baseStart_4654122 : Nat := 118140960795 + 4654122 * 2 ^ 59
def prefixEnd_4654122 : Nat := 4983230072969 + 3 ^ 40 * 4654122 * 2
def baseEnd_4654122 : Nat := 265533512296082773330121

theorem tailTrace_4654122 : CollatzResearch.WordTrace tailWord_4654122 prefixEnd_4654122 265533512296082773330121 := by
  unfold tailWord_4654122
  simp only [CollatzResearch.WordTrace]
  refine ⟨42437443711229582400153155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113166516563278886400408413 42437443711229582400153155)
  ·
    refine ⟨63656165566844373600229733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42437443711229582400153155 63656165566844373600229733)
    ·
      refine ⟨11935531043783320050043075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63656165566844373600229733 11935531043783320050043075)
      ·
        refine ⟨17903296565674980075064613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11935531043783320050043075 17903296565674980075064613)
        ·
          refine ⟨3356868106064058764074615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17903296565674980075064613 3356868106064058764074615)
          ·
            refine ⟨5035302159096088146111923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3356868106064058764074615 5035302159096088146111923)
            ·
              refine ⟨7552953238644132219167885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5035302159096088146111923 7552953238644132219167885)
              ·
                refine ⟨2832357464491549582187957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7552953238644132219167885 2832357464491549582187957)
                ·
                  refine ⟨265533512296082773330121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2832357464491549582187957 265533512296082773330121)
                  ·
                    rfl

theorem cell23_4654122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 3, 5].length) (baseStart_4654122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4654122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4654122 prefixEnd_4654122 := by exact prefixLift 4654122
  have htrace : WordTrace (prefixWord ++ tailWord_4654122) baseStart_4654122 baseEnd_4654122 := by
    simpa [prefixWord, tailWord_4654122, baseEnd_4654122] using wordTrace_append hprefix tailTrace_4654122
  have hstable : (prefixWord ++ tailWord_4654122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4654122).length < 2 ^ (prefixWord ++ tailWord_4654122).sum := by decide
  have hdescent : baseEnd_4654122 < baseStart_4654122 := by decide
  rcases family_descends (prefixWord ++ tailWord_4654122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4654144 : List Nat := [2, 1, 1, 2, 2, 3, 1, 3, 8]
def baseStart_4654144 : Nat := 118140960795 + 4654144 * 2 ^ 59
def prefixEnd_4654144 : Nat := 4983230072969 + 3 ^ 40 * 4654144 * 2
def baseEnd_4654144 : Nat := 265534767471015985988443

theorem tailTrace_4654144 : CollatzResearch.WordTrace tailWord_4654144 prefixEnd_4654144 265534767471015985988443 := by
  unfold tailWord_4654144
  simp only [CollatzResearch.WordTrace]
  refine ⟨84875288625419313678956743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113167051500559084905275657 84875288625419313678956743)
  ·
    refine ⟨127312932938128970518435115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84875288625419313678956743 127312932938128970518435115)
    ·
      refine ⟨190969399407193455777652673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127312932938128970518435115 190969399407193455777652673)
      ·
        refine ⟨143227049555395091833239505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190969399407193455777652673 143227049555395091833239505)
        ·
          refine ⟨107420287166546318874929629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143227049555395091833239505 107420287166546318874929629)
          ·
            refine ⟨40282607687454869578098611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107420287166546318874929629 40282607687454869578098611)
            ·
              refine ⟨60423911531182304367147917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40282607687454869578098611 60423911531182304367147917)
              ·
                refine ⟨22658966824193364137680469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60423911531182304367147917 22658966824193364137680469)
                ·
                  refine ⟨265534767471015985988443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22658966824193364137680469 265534767471015985988443)
                  ·
                    rfl

theorem cell23_4654144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 8].length) (baseStart_4654144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4654144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4654144 prefixEnd_4654144 := by exact prefixLift 4654144
  have htrace : WordTrace (prefixWord ++ tailWord_4654144) baseStart_4654144 baseEnd_4654144 := by
    simpa [prefixWord, tailWord_4654144, baseEnd_4654144] using wordTrace_append hprefix tailTrace_4654144
  have hstable : (prefixWord ++ tailWord_4654144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4654144).length < 2 ^ (prefixWord ++ tailWord_4654144).sum := by decide
  have hdescent : baseEnd_4654144 < baseStart_4654144 := by decide
  rcases family_descends (prefixWord ++ tailWord_4654144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4654211 : List Nat := [1, 1, 1, 3, 3, 2, 1, 1, 5, 1, 4]
def baseStart_4654211 : Nat := 118140960795 + 4654211 * 2 ^ 59
def prefixEnd_4654211 : Nat := 4983230072969 + 3 ^ 40 * 4654211 * 2
def baseEnd_4654211 : Nat := 2389847310442995111758179

theorem tailTrace_4654211 : CollatzResearch.WordTrace tailWord_4654211 prefixEnd_4654211 2389847310442995111758179 := by
  unfold tailWord_4654211
  simp only [CollatzResearch.WordTrace]
  refine ⟨169753020941595897800602487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113168680627730598533734991 169753020941595897800602487)
  ·
    refine ⟨254629531412393846700903731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169753020941595897800602487 254629531412393846700903731)
    ·
      refine ⟨381944297118590770051355597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254629531412393846700903731 381944297118590770051355597)
      ·
        refine ⟨143229111419471538769258349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 381944297118590770051355597 143229111419471538769258349)
        ·
          refine ⟨53710916782301827038471881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 143229111419471538769258349 53710916782301827038471881)
          ·
            refine ⟨40283187586726370278853911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53710916782301827038471881 40283187586726370278853911)
            ·
              refine ⟨60424781380089555418280867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40283187586726370278853911 60424781380089555418280867)
              ·
                refine ⟨90637172070134333127421301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60424781380089555418280867 90637172070134333127421301)
                ·
                  refine ⟨8497234881575093730695747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 90637172070134333127421301 8497234881575093730695747)
                  ·
                    refine ⟨12745852322362640596043621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8497234881575093730695747 12745852322362640596043621)
                    ·
                      refine ⟨2389847310442995111758179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12745852322362640596043621 2389847310442995111758179)
                      ·
                        rfl

theorem cell23_4654211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 5, 1, 4].length) (baseStart_4654211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4654211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4654211 prefixEnd_4654211 := by exact prefixLift 4654211
  have htrace : WordTrace (prefixWord ++ tailWord_4654211) baseStart_4654211 baseEnd_4654211 := by
    simpa [prefixWord, tailWord_4654211, baseEnd_4654211] using wordTrace_append hprefix tailTrace_4654211
  have hstable : (prefixWord ++ tailWord_4654211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4654211).length < 2 ^ (prefixWord ++ tailWord_4654211).sum := by decide
  have hdescent : baseEnd_4654211 < baseStart_4654211 := by decide
  rcases family_descends (prefixWord ++ tailWord_4654211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4654232 : List Nat := [2, 1, 2, 4, 2, 3, 1, 1, 2, 3, 2]
def baseStart_4654232 : Nat := 118140960795 + 4654232 * 2 ^ 59
def prefixEnd_4654232 : Nat := 4983230072969 + 3 ^ 40 * 4654232 * 2
def baseEnd_4654232 : Nat := 2389858093536739529595583

theorem tailTrace_4654232 : CollatzResearch.WordTrace tailWord_4654232 prefixEnd_4654232 2389858093536739529595583 := by
  unfold tailWord_4654232
  simp only [CollatzResearch.WordTrace]
  refine ⟨84876893437259909193558475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113169191249679878924744633 84876893437259909193558475)
  ·
    refine ⟨127315340155889863790337713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84876893437259909193558475 127315340155889863790337713)
    ·
      refine ⟨95486505116917397842753285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127315340155889863790337713 95486505116917397842753285)
      ·
        refine ⟨17903719709422012095516241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95486505116917397842753285 17903719709422012095516241)
        ·
          refine ⟨13427789782066509071637181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17903719709422012095516241 13427789782066509071637181)
          ·
            refine ⟨5035421168274940901863943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13427789782066509071637181 5035421168274940901863943)
            ·
              refine ⟨7553131752412411352795915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5035421168274940901863943 7553131752412411352795915)
              ·
                refine ⟨11329697628618617029193873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7553131752412411352795915 11329697628618617029193873)
                ·
                  refine ⟨8497273221463962771895405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11329697628618617029193873 8497273221463962771895405)
                  ·
                    refine ⟨3186477458048986039460777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8497273221463962771895405 3186477458048986039460777)
                    ·
                      refine ⟨2389858093536739529595583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3186477458048986039460777 2389858093536739529595583)
                      ·
                        rfl

theorem cell23_4654232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 1, 2, 3, 2].length) (baseStart_4654232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4654232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4654232 prefixEnd_4654232 := by exact prefixLift 4654232
  have htrace : WordTrace (prefixWord ++ tailWord_4654232) baseStart_4654232 baseEnd_4654232 := by
    simpa [prefixWord, tailWord_4654232, baseEnd_4654232] using wordTrace_append hprefix tailTrace_4654232
  have hstable : (prefixWord ++ tailWord_4654232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4654232).length < 2 ^ (prefixWord ++ tailWord_4654232).sum := by decide
  have hdescent : baseEnd_4654232 < baseStart_4654232 := by decide
  rcases family_descends (prefixWord ++ tailWord_4654232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4654239 : List Nat := [1, 1, 2, 6, 2, 1, 2, 3, 1, 1, 3]
def baseStart_4654239 : Nat := 118140960795 + 4654239 * 2 ^ 59
def prefixEnd_4654239 : Nat := 4983230072969 + 3 ^ 40 * 4654239 * 2
def baseEnd_4654239 : Nat := 2389861687901321002208051

theorem tailTrace_4654239 : CollatzResearch.WordTrace tailWord_4654239 prefixEnd_4654239 2389861687901321002208051 := by
  unfold tailWord_4654239
  simp only [CollatzResearch.WordTrace]
  refine ⟨169754042185494458582621771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113169361456996305721747847 169754042185494458582621771)
  ·
    refine ⟨254631063278241687873932657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169754042185494458582621771 254631063278241687873932657)
    ·
      refine ⟨190973297458681265905449493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 254631063278241687873932657 190973297458681265905449493)
      ·
        refine ⟨8951873318375684339317945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 190973297458681265905449493 8951873318375684339317945)
        ·
          refine ⟨6713904988781763254488459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8951873318375684339317945 6713904988781763254488459)
          ·
            refine ⟨10070857483172644881732689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6713904988781763254488459 10070857483172644881732689)
            ·
              refine ⟨7553143112379483661299517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10070857483172644881732689 7553143112379483661299517)
              ·
                refine ⟨2832428667142306372987319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7553143112379483661299517 2832428667142306372987319)
                ·
                  refine ⟨4248643000713459559480979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2832428667142306372987319 4248643000713459559480979)
                  ·
                    refine ⟨6372964501070189339221469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4248643000713459559480979 6372964501070189339221469)
                    ·
                      refine ⟨2389861687901321002208051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6372964501070189339221469 2389861687901321002208051)
                      ·
                        rfl

theorem cell23_4654239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_4654239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4654239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4654239 prefixEnd_4654239 := by exact prefixLift 4654239
  have htrace : WordTrace (prefixWord ++ tailWord_4654239) baseStart_4654239 baseEnd_4654239 := by
    simpa [prefixWord, tailWord_4654239, baseEnd_4654239] using wordTrace_append hprefix tailTrace_4654239
  have hstable : (prefixWord ++ tailWord_4654239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4654239).length < 2 ^ (prefixWord ++ tailWord_4654239).sum := by decide
  have hdescent : baseEnd_4654239 < baseStart_4654239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4654239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4654245 : List Nat := [1, 3, 1, 2, 1, 4, 4, 1, 1, 1, 4]
def baseStart_4654245 : Nat := 118140960795 + 4654245 * 2 ^ 59
def prefixEnd_4654245 : Nat := 4983230072969 + 3 ^ 40 * 4654245 * 2
def baseEnd_4654245 : Nat := 2389864768785247978733023

theorem tailTrace_4654245 : CollatzResearch.WordTrace tailWord_4654245 prefixEnd_4654245 2389864768785247978733023 := by
  unfold tailWord_4654245
  simp only [CollatzResearch.WordTrace]
  refine ⟨169754261023472721607340189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113169507348981814404893459 169754261023472721607340189)
  ·
    refine ⟨63657847883802270602752571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169754261023472721607340189 63657847883802270602752571)
    ·
      refine ⟨95486771825703405904128857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63657847883802270602752571 95486771825703405904128857)
      ·
        refine ⟨71615078869277554428096643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95486771825703405904128857 71615078869277554428096643)
        ·
          refine ⟨107422618303916331642144965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71615078869277554428096643 107422618303916331642144965)
          ·
            refine ⟨20141740931984312182902181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 107422618303916331642144965 20141740931984312182902181)
            ·
              refine ⟨3776576424747058534294159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20141740931984312182902181 3776576424747058534294159)
              ·
                refine ⟨5664864637120587801441239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3776576424747058534294159 5664864637120587801441239)
                ·
                  refine ⟨8497296955680881702161859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5664864637120587801441239 8497296955680881702161859)
                  ·
                    refine ⟨12745945433521322553242789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8497296955680881702161859 12745945433521322553242789)
                    ·
                      refine ⟨2389864768785247978733023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12745945433521322553242789 2389864768785247978733023)
                      ·
                        rfl

theorem cell23_4654245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 4, 1, 1, 1, 4].length) (baseStart_4654245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4654245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4654245 prefixEnd_4654245 := by exact prefixLift 4654245
  have htrace : WordTrace (prefixWord ++ tailWord_4654245) baseStart_4654245 baseEnd_4654245 := by
    simpa [prefixWord, tailWord_4654245, baseEnd_4654245] using wordTrace_append hprefix tailTrace_4654245
  have hstable : (prefixWord ++ tailWord_4654245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4654245).length < 2 ^ (prefixWord ++ tailWord_4654245).sum := by decide
  have hdescent : baseEnd_4654245 < baseStart_4654245 := by decide
  rcases family_descends (prefixWord ++ tailWord_4654245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4654272 : List Nat := [2, 1, 1, 2, 6, 1, 3, 1, 2, 4]
def baseStart_4654272 : Nat := 118140960795 + 4654272 * 2 ^ 59
def prefixEnd_4654272 : Nat := 4983230072969 + 3 ^ 40 * 4654272 * 2
def baseEnd_4654272 : Nat := 796626210920973124365133

theorem tailTrace_4654272 : CollatzResearch.WordTrace tailWord_4654272 prefixEnd_4654272 796626210920973124365133 := by
  unfold tailWord_4654272
  simp only [CollatzResearch.WordTrace]
  refine ⟨84877622897187452609286535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113170163862916603479048713 84877622897187452609286535)
  ·
    refine ⟨127316434345781178913929803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84877622897187452609286535 127316434345781178913929803)
    ·
      refine ⟨190974651518671768370894705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127316434345781178913929803 190974651518671768370894705)
      ·
        refine ⟨143230988639003826278171029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190974651518671768370894705 143230988639003826278171029)
        ·
          refine ⟨6713952592453304356789267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 143230988639003826278171029 6713952592453304356789267)
          ·
            refine ⟨10070928888679956535183901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6713952592453304356789267 10070928888679956535183901)
            ·
              refine ⟨3776598333254983700693963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10070928888679956535183901 3776598333254983700693963)
              ·
                refine ⟨5664897499882475551040945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3776598333254983700693963 5664897499882475551040945)
                ·
                  refine ⟨4248673124911856663280709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5664897499882475551040945 4248673124911856663280709)
                  ·
                    refine ⟨796626210920973124365133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4248673124911856663280709 796626210920973124365133)
                    ·
                      rfl

theorem cell23_4654272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 3, 1, 2, 4].length) (baseStart_4654272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4654272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4654272 prefixEnd_4654272 := by exact prefixLift 4654272
  have htrace : WordTrace (prefixWord ++ tailWord_4654272) baseStart_4654272 baseEnd_4654272 := by
    simpa [prefixWord, tailWord_4654272, baseEnd_4654272] using wordTrace_append hprefix tailTrace_4654272
  have hstable : (prefixWord ++ tailWord_4654272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4654272).length < 2 ^ (prefixWord ++ tailWord_4654272).sum := by decide
  have hdescent : baseEnd_4654272 < baseStart_4654272 := by decide
  rcases family_descends (prefixWord ++ tailWord_4654272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4654296 : List Nat := [2, 1, 2, 2, 5, 2, 1, 3, 1, 2, 2]
def baseStart_4654296 : Nat := 118140960795 + 4654296 * 2 ^ 59
def prefixEnd_4654296 : Nat := 4983230072969 + 3 ^ 40 * 4654296 * 2
def baseEnd_4654296 : Nat := 2389890956298627279195289

theorem tailTrace_4654296 : CollatzResearch.WordTrace tailWord_4654296 prefixEnd_4654296 2389890956298627279195289 := by
  unfold tailWord_4654296
  simp only [CollatzResearch.WordTrace]
  refine ⟨84878060573143978658723371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113170747430858638211631161 84878060573143978658723371)
  ·
    refine ⟨127317090859715967988085057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84878060573143978658723371 127317090859715967988085057)
    ·
      refine ⟨95487818144786975991063793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127317090859715967988085057 95487818144786975991063793)
      ·
        refine ⟨71615863608590231993297845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95487818144786975991063793 71615863608590231993297845)
        ·
          refine ⟨6713987213305334249371673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 71615863608590231993297845 6713987213305334249371673)
          ·
            refine ⟨5035490409979000687028755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6713987213305334249371673 5035490409979000687028755)
            ·
              refine ⟨7553235614968501030543133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5035490409979000687028755 7553235614968501030543133)
              ·
                refine ⟨2832463355613187886453675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7553235614968501030543133 2832463355613187886453675)
                ·
                  refine ⟨4248695033419781829680513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2832463355613187886453675 4248695033419781829680513)
                  ·
                    refine ⟨3186521275064836372260385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4248695033419781829680513 3186521275064836372260385)
                    ·
                      refine ⟨2389890956298627279195289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3186521275064836372260385 2389890956298627279195289)
                      ·
                        rfl

theorem cell23_4654296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 3, 1, 2, 2].length) (baseStart_4654296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4654296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4654296 prefixEnd_4654296 := by exact prefixLift 4654296
  have htrace : WordTrace (prefixWord ++ tailWord_4654296) baseStart_4654296 baseEnd_4654296 := by
    simpa [prefixWord, tailWord_4654296, baseEnd_4654296] using wordTrace_append hprefix tailTrace_4654296
  have hstable : (prefixWord ++ tailWord_4654296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4654296).length < 2 ^ (prefixWord ++ tailWord_4654296).sum := by decide
  have hdescent : baseEnd_4654296 < baseStart_4654296 := by decide
  rcases family_descends (prefixWord ++ tailWord_4654296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4654321 : List Nat := [1, 2, 2, 2, 2, 1, 1, 1, 3, 3, 5]
def baseStart_4654321 : Nat := 118140960795 + 4654321 * 2 ^ 59
def prefixEnd_4654321 : Nat := 4983230072969 + 3 ^ 40 * 4654321 * 2
def baseEnd_4654321 : Nat := 2389903793314989681382673

theorem tailTrace_4654321 : CollatzResearch.WordTrace tailWord_4654321 prefixEnd_4654321 2389903793314989681382673 := by
  unfold tailWord_4654321
  simp only [CollatzResearch.WordTrace]
  refine ⟨169757032971197386587106817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113171355314131591058071211 169757032971197386587106817)
  ·
    refine ⟨127317774728398039940330113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169757032971197386587106817 127317774728398039940330113)
    ·
      refine ⟨95488331046298529955247585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127317774728398039940330113 95488331046298529955247585)
      ·
        refine ⟨71616248284723897466435689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95488331046298529955247585 71616248284723897466435689)
        ·
          refine ⟨53712186213542923099826767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71616248284723897466435689 53712186213542923099826767)
          ·
            refine ⟨80568279320314384649740151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53712186213542923099826767 80568279320314384649740151)
            ·
              refine ⟨120852418980471576974610227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80568279320314384649740151 120852418980471576974610227)
              ·
                refine ⟨181278628470707365461915341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120852418980471576974610227 181278628470707365461915341)
                ·
                  refine ⟨67979485676515262048218253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 181278628470707365461915341 67979485676515262048218253)
                  ·
                    refine ⟨25492307128693223268081845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 67979485676515262048218253 25492307128693223268081845)
                    ·
                      refine ⟨2389903793314989681382673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25492307128693223268081845 2389903793314989681382673)
                      ·
                        rfl

theorem cell23_4654321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_4654321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4654321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4654321 prefixEnd_4654321 := by exact prefixLift 4654321
  have htrace : WordTrace (prefixWord ++ tailWord_4654321) baseStart_4654321 baseEnd_4654321 := by
    simpa [prefixWord, tailWord_4654321, baseEnd_4654321] using wordTrace_append hprefix tailTrace_4654321
  have hstable : (prefixWord ++ tailWord_4654321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4654321).length < 2 ^ (prefixWord ++ tailWord_4654321).sum := by decide
  have hdescent : baseEnd_4654321 < baseStart_4654321 := by decide
  rcases family_descends (prefixWord ++ tailWord_4654321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4654341 : List Nat := [1, 3, 1, 1, 2, 1, 4, 1, 9]
def baseStart_4654341 : Nat := 118140960795 + 4654341 * 2 ^ 59
def prefixEnd_4654341 : Nat := 4983230072969 + 3 ^ 40 * 4654341 * 2
def baseEnd_4654341 : Nat := 265546006992008844792509

theorem tailTrace_4654341 : CollatzResearch.WordTrace tailWord_4654341 prefixEnd_4654341 265546006992008844792509 := by
  unfold tailWord_4654341
  simp only [CollatzResearch.WordTrace]
  refine ⟨169757762431124930002834877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113171841620749953335223251 169757762431124930002834877)
  ·
    refine ⟨63659160911671848751063079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169757762431124930002834877 63659160911671848751063079)
    ·
      refine ⟨95488741367507773126594619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63659160911671848751063079 95488741367507773126594619)
      ·
        refine ⟨143233112051261659689891929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95488741367507773126594619 143233112051261659689891929)
        ·
          refine ⟨107424834038446244767418947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143233112051261659689891929 107424834038446244767418947)
          ·
            refine ⟨161137251057669367151128421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107424834038446244767418947 161137251057669367151128421)
            ·
              refine ⟨30213234573313006340836579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 161137251057669367151128421 30213234573313006340836579)
              ·
                refine ⟨45319851859969509511254869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30213234573313006340836579 45319851859969509511254869)
                ·
                  refine ⟨265546006992008844792509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 45319851859969509511254869 265546006992008844792509)
                  ·
                    rfl

theorem cell23_4654341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 9].length) (baseStart_4654341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4654341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4654341 prefixEnd_4654341 := by exact prefixLift 4654341
  have htrace : WordTrace (prefixWord ++ tailWord_4654341) baseStart_4654341 baseEnd_4654341 := by
    simpa [prefixWord, tailWord_4654341, baseEnd_4654341] using wordTrace_append hprefix tailTrace_4654341
  have hstable : (prefixWord ++ tailWord_4654341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4654341).length < 2 ^ (prefixWord ++ tailWord_4654341).sum := by decide
  have hdescent : baseEnd_4654341 < baseStart_4654341 := by decide
  rcases family_descends (prefixWord ++ tailWord_4654341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4654385 : List Nat := [1, 2, 2, 3, 3, 2, 1, 1, 2, 3, 3]
def baseStart_4654385 : Nat := 118140960795 + 4654385 * 2 ^ 59
def prefixEnd_4654385 : Nat := 4983230072969 + 3 ^ 40 * 4654385 * 2
def baseEnd_4654385 : Nat := 2389936656076877430982379

theorem tailTrace_4654385 : CollatzResearch.WordTrace tailWord_4654385 prefixEnd_4654385 2389936656076877430982379 := by
  unfold tailWord_4654385
  simp only [CollatzResearch.WordTrace]
  refine ⟨169759367242965525517436609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113172911495310350344957739 169759367242965525517436609)
  ·
    refine ⟨127319525432224144138077457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169759367242965525517436609 127319525432224144138077457)
    ·
      refine ⟨95489644074168108103558093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127319525432224144138077457 95489644074168108103558093)
      ·
        refine ⟨35808616527813040538834285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95489644074168108103558093 35808616527813040538834285)
        ·
          refine ⟨13428231197929890202062857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35808616527813040538834285 13428231197929890202062857)
          ·
            refine ⟨10071173398447417651547143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13428231197929890202062857 10071173398447417651547143)
            ·
              refine ⟨15106760097671126477320715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10071173398447417651547143 15106760097671126477320715)
              ·
                refine ⟨22660140146506689715981073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15106760097671126477320715 22660140146506689715981073)
                ·
                  refine ⟨16995105109880017286985805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22660140146506689715981073 16995105109880017286985805)
                  ·
                    refine ⟨6373164416205006482619677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16995105109880017286985805 6373164416205006482619677)
                    ·
                      refine ⟨2389936656076877430982379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6373164416205006482619677 2389936656076877430982379)
                      ·
                        rfl

theorem cell23_4654385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 2, 3, 3].length) (baseStart_4654385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4654385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4654385 prefixEnd_4654385 := by exact prefixLift 4654385
  have htrace : WordTrace (prefixWord ++ tailWord_4654385) baseStart_4654385 baseEnd_4654385 := by
    simpa [prefixWord, tailWord_4654385, baseEnd_4654385] using wordTrace_append hprefix tailTrace_4654385
  have hstable : (prefixWord ++ tailWord_4654385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4654385).length < 2 ^ (prefixWord ++ tailWord_4654385).sum := by decide
  have hdescent : baseEnd_4654385 < baseStart_4654385 := by decide
  rcases family_descends (prefixWord ++ tailWord_4654385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4654425 : List Nat := [1, 2, 1, 2, 2, 2, 3, 2, 2, 4, 2]
def baseStart_4654425 : Nat := 118140960795 + 4654425 * 2 ^ 59
def prefixEnd_4654425 : Nat := 4983230072969 + 3 ^ 40 * 4654425 * 2
def baseEnd_4654425 : Nat := 2389957195303057274482195

theorem tailTrace_4654425 : CollatzResearch.WordTrace tailWord_4654425 prefixEnd_4654425 2389957195303057274482195 := by
  unfold tailWord_4654425
  simp only [CollatzResearch.WordTrace]
  refine ⟨169760826162820612348892729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113173884108547074899261819 169760826162820612348892729)
  ·
    refine ⟨127320619622115459261669547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169760826162820612348892729 127320619622115459261669547)
    ·
      refine ⟨190980929433173188892504321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127320619622115459261669547 190980929433173188892504321)
      ·
        refine ⟨143235697074879891669378241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190980929433173188892504321 143235697074879891669378241)
        ·
          refine ⟨107426772806159918752033681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143235697074879891669378241 107426772806159918752033681)
          ·
            refine ⟨80570079604619939064025261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107426772806159918752033681 80570079604619939064025261)
            ·
              refine ⟨30213779851732477149009473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80570079604619939064025261 30213779851732477149009473)
              ·
                refine ⟨22660334888799357861757105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30213779851732477149009473 22660334888799357861757105)
                ·
                  refine ⟨16995251166599518396317829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22660334888799357861757105 16995251166599518396317829)
                  ·
                    refine ⟨3186609593737409699309593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16995251166599518396317829 3186609593737409699309593)
                    ·
                      refine ⟨2389957195303057274482195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3186609593737409699309593 2389957195303057274482195)
                      ·
                        rfl

theorem cell23_4654425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 2, 4, 2].length) (baseStart_4654425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4654425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4654425 prefixEnd_4654425 := by exact prefixLift 4654425
  have htrace : WordTrace (prefixWord ++ tailWord_4654425) baseStart_4654425 baseEnd_4654425 := by
    simpa [prefixWord, tailWord_4654425, baseEnd_4654425] using wordTrace_append hprefix tailTrace_4654425
  have hstable : (prefixWord ++ tailWord_4654425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4654425).length < 2 ^ (prefixWord ++ tailWord_4654425).sum := by decide
  have hdescent : baseEnd_4654425 < baseStart_4654425 := by decide
  rcases family_descends (prefixWord ++ tailWord_4654425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4654435 : List Nat := [1, 1, 1, 5, 2, 2, 1, 3, 3, 4]
def baseStart_4654435 : Nat := 118140960795 + 4654435 * 2 ^ 59
def prefixEnd_4654435 : Nat := 4983230072969 + 3 ^ 40 * 4654435 * 2
def baseEnd_4654435 : Nat := 796654110036534078452383

theorem tailTrace_4654435 : CollatzResearch.WordTrace tailWord_4654435 prefixEnd_4654435 796654110036534078452383 := by
  unfold tailWord_4654435
  simp only [CollatzResearch.WordTrace]
  refine ⟨169761190892784384056756759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113174127261856256037837839 169761190892784384056756759)
  ·
    refine ⟨254641786339176576085135139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169761190892784384056756759 254641786339176576085135139)
    ·
      refine ⟨381962679508764864127702709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254641786339176576085135139 381962679508764864127702709)
      ·
        refine ⟨35809001203946706011972129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 381962679508764864127702709 35809001203946706011972129)
        ·
          refine ⟨26856750902960029508979097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35809001203946706011972129 26856750902960029508979097)
          ·
            refine ⟨20142563177220022131734323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26856750902960029508979097 20142563177220022131734323)
            ·
              refine ⟨30213844765830033197601485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20142563177220022131734323 30213844765830033197601485)
              ·
                refine ⟨11330191787186262449100557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30213844765830033197601485 11330191787186262449100557)
                ·
                  refine ⟨4248821920194848418412709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11330191787186262449100557 4248821920194848418412709)
                  ·
                    refine ⟨796654110036534078452383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4248821920194848418412709 796654110036534078452383)
                    ·
                      rfl

theorem cell23_4654435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 3, 3, 4].length) (baseStart_4654435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4654435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4654435 prefixEnd_4654435 := by exact prefixLift 4654435
  have htrace : WordTrace (prefixWord ++ tailWord_4654435) baseStart_4654435 baseEnd_4654435 := by
    simpa [prefixWord, tailWord_4654435, baseEnd_4654435] using wordTrace_append hprefix tailTrace_4654435
  have hstable : (prefixWord ++ tailWord_4654435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4654435).length < 2 ^ (prefixWord ++ tailWord_4654435).sum := by decide
  have hdescent : baseEnd_4654435 < baseStart_4654435 := by decide
  rcases family_descends (prefixWord ++ tailWord_4654435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4654445 : List Nat := [1, 5, 1, 1, 1, 3, 1, 2, 1, 4, 3]
def baseStart_4654445 : Nat := 118140960795 + 4654445 * 2 ^ 59
def prefixEnd_4654445 : Nat := 4983230072969 + 3 ^ 40 * 4654445 * 2
def baseEnd_4654445 : Nat := 2389967464916147196232103

theorem tailTrace_4654445 : CollatzResearch.WordTrace tailWord_4654445 prefixEnd_4654445 2389967464916147196232103 := by
  unfold tailWord_4654445
  simp only [CollatzResearch.WordTrace]
  refine ⟨169761555622748155764620789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113174370415165437176413859 169761555622748155764620789)
  ·
    refine ⟨15915145839632639602933199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 169761555622748155764620789 15915145839632639602933199)
    ·
      refine ⟨23872718759448959404399799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15915145839632639602933199 23872718759448959404399799)
      ·
        refine ⟨35809078139173439106599699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23872718759448959404399799 35809078139173439106599699)
        ·
          refine ⟨53713617208760158659899549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35809078139173439106599699 53713617208760158659899549)
          ·
            refine ⟨20142606453285059497462331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53713617208760158659899549 20142606453285059497462331)
            ·
              refine ⟨30213909679927589246193497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20142606453285059497462331 30213909679927589246193497)
              ·
                refine ⟨22660432259945691934645123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30213909679927589246193497 22660432259945691934645123)
                ·
                  refine ⟨33990648389918537901967685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22660432259945691934645123 33990648389918537901967685)
                  ·
                    refine ⟨6373246573109725856618941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33990648389918537901967685 6373246573109725856618941)
                    ·
                      refine ⟨2389967464916147196232103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6373246573109725856618941 2389967464916147196232103)
                      ·
                        rfl

theorem cell23_4654445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 4, 3].length) (baseStart_4654445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4654445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4654445 prefixEnd_4654445 := by exact prefixLift 4654445
  have htrace : WordTrace (prefixWord ++ tailWord_4654445) baseStart_4654445 baseEnd_4654445 := by
    simpa [prefixWord, tailWord_4654445, baseEnd_4654445] using wordTrace_append hprefix tailTrace_4654445
  have hstable : (prefixWord ++ tailWord_4654445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4654445).length < 2 ^ (prefixWord ++ tailWord_4654445).sum := by decide
  have hdescent : baseEnd_4654445 < baseStart_4654445 := by decide
  rcases family_descends (prefixWord ++ tailWord_4654445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4654515 : List Nat := [1, 1, 1, 2, 3, 1, 1, 3, 2, 6, 2]
def baseStart_4654515 : Nat := 118140960795 + 4654515 * 2 ^ 59
def prefixEnd_4654515 : Nat := 4983230072969 + 3 ^ 40 * 4654515 * 2
def baseEnd_4654515 : Nat := 2390003408561961922356781

theorem tailTrace_4654515 : CollatzResearch.WordTrace tailWord_4654515 prefixEnd_4654515 2390003408561961922356781 := by
  unfold tailWord_4654515
  simp only [CollatzResearch.WordTrace]
  refine ⟨169764108732494557719668999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113176072488329705146445999 169764108732494557719668999)
  ·
    refine ⟨254646163098741836579503499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169764108732494557719668999 254646163098741836579503499)
    ·
      refine ⟨381969244648112754869255249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254646163098741836579503499 381969244648112754869255249)
      ·
        refine ⟨286476933486084566151941437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 381969244648112754869255249 286476933486084566151941437)
        ·
          refine ⟨107428850057281712306978039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 286476933486084566151941437 107428850057281712306978039)
          ·
            refine ⟨161143275085922568460467059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107428850057281712306978039 161143275085922568460467059)
            ·
              refine ⟨241714912628883852690700589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161143275085922568460467059 241714912628883852690700589)
              ·
                refine ⟨90643092235831444759012721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 241714912628883852690700589 90643092235831444759012721)
                ·
                  refine ⟨67982319176873583569259541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90643092235831444759012721 67982319176873583569259541)
                  ·
                    refine ⟨3186671211415949229809041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 67982319176873583569259541 3186671211415949229809041)
                    ·
                      refine ⟨2390003408561961922356781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3186671211415949229809041 2390003408561961922356781)
                      ·
                        rfl

theorem cell23_4654515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 6, 2].length) (baseStart_4654515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4654515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4654515 prefixEnd_4654515 := by exact prefixLift 4654515
  have htrace : WordTrace (prefixWord ++ tailWord_4654515) baseStart_4654515 baseEnd_4654515 := by
    simpa [prefixWord, tailWord_4654515, baseEnd_4654515] using wordTrace_append hprefix tailTrace_4654515
  have hstable : (prefixWord ++ tailWord_4654515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4654515).length < 2 ^ (prefixWord ++ tailWord_4654515).sum := by decide
  have hdescent : baseEnd_4654515 < baseStart_4654515 := by decide
  rcases family_descends (prefixWord ++ tailWord_4654515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4654525 : List Nat := [1, 4, 1, 2, 2, 1, 3, 2, 1, 6]
def baseStart_4654525 : Nat := 118140960795 + 4654525 * 2 ^ 59
def prefixEnd_4654525 : Nat := 4983230072969 + 3 ^ 40 * 4654525 * 2
def baseEnd_4654525 : Nat := 796669514456168961077245

theorem tailTrace_4654525 : CollatzResearch.WordTrace tailWord_4654525 prefixEnd_4654525 796669514456168961077245 := by
  unfold tailWord_4654525
  simp only [CollatzResearch.WordTrace]
  refine ⟨169764473462458329427533029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113176315641638886285022019 169764473462458329427533029)
  ·
    refine ⟨31830838774210936767662443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 169764473462458329427533029 31830838774210936767662443)
    ·
      refine ⟨47746258161316405151493665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31830838774210936767662443 47746258161316405151493665)
      ·
        refine ⟨35809693620987303863620249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47746258161316405151493665 35809693620987303863620249)
        ·
          refine ⟨26857270215740477897715187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35809693620987303863620249 26857270215740477897715187)
          ·
            refine ⟨40285905323610716846572781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26857270215740477897715187 40285905323610716846572781)
            ·
              refine ⟨15107214496354018817464793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40285905323610716846572781 15107214496354018817464793)
              ·
                refine ⟨11330410872265514113098595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15107214496354018817464793 11330410872265514113098595)
                ·
                  refine ⟨16995616308398271169647893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11330410872265514113098595 16995616308398271169647893)
                  ·
                    refine ⟨796669514456168961077245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16995616308398271169647893 796669514456168961077245)
                    ·
                      rfl

theorem cell23_4654525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 2, 1, 6].length) (baseStart_4654525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4654525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4654525 prefixEnd_4654525 := by exact prefixLift 4654525
  have htrace : WordTrace (prefixWord ++ tailWord_4654525) baseStart_4654525 baseEnd_4654525 := by
    simpa [prefixWord, tailWord_4654525, baseEnd_4654525] using wordTrace_append hprefix tailTrace_4654525
  have hstable : (prefixWord ++ tailWord_4654525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4654525).length < 2 ^ (prefixWord ++ tailWord_4654525).sum := by decide
  have hdescent : baseEnd_4654525 < baseStart_4654525 := by decide
  rcases family_descends (prefixWord ++ tailWord_4654525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4654538 : List Nat := [3, 1, 2, 1, 2, 14]
def baseStart_4654538 : Nat := 118140960795 + 4654538 * 2 ^ 59
def prefixEnd_4654538 : Nat := 4983230072969 + 3 ^ 40 * 4654538 * 2
def baseEnd_4654538 : Nat := 9835453574555618651725

theorem tailTrace_4654538 : CollatzResearch.WordTrace tailWord_4654538 prefixEnd_4654538 9835453574555618651725 := by
  unfold tailWord_4654538
  simp only [CollatzResearch.WordTrace]
  refine ⟨42441236902852808161939067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113176631740940821765170845 42441236902852808161939067)
  ·
    refine ⟨63661855354279212242908601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42441236902852808161939067 63661855354279212242908601)
    ·
      refine ⟨47746391515709409182181451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63661855354279212242908601 47746391515709409182181451)
      ·
        refine ⟨71619587273564113773272177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47746391515709409182181451 71619587273564113773272177)
        ·
          refine ⟨53714690455173085329954133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71619587273564113773272177 53714690455173085329954133)
          ·
            refine ⟨9835453574555618651725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 53714690455173085329954133 9835453574555618651725)
            ·
              rfl

theorem cell23_4654538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 14].length) (baseStart_4654538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4654538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4654538 prefixEnd_4654538 := by exact prefixLift 4654538
  have htrace : WordTrace (prefixWord ++ tailWord_4654538) baseStart_4654538 baseEnd_4654538 := by
    simpa [prefixWord, tailWord_4654538, baseEnd_4654538] using wordTrace_append hprefix tailTrace_4654538
  have hstable : (prefixWord ++ tailWord_4654538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4654538).length < 2 ^ (prefixWord ++ tailWord_4654538).sum := by decide
  have hdescent : baseEnd_4654538 < baseStart_4654538 := by decide
  rcases family_descends (prefixWord ++ tailWord_4654538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4654542 : List Nat := [4, 1, 1, 1, 2, 1, 3, 4, 2, 4]
def baseStart_4654542 : Nat := 118140960795 + 4654542 * 2 ^ 59
def prefixEnd_4654542 : Nat := 4983230072969 + 3 ^ 40 * 4654542 * 2
def baseEnd_4654542 : Nat := 796672424179877772239719

theorem tailTrace_4654542 : CollatzResearch.WordTrace tailWord_4654542 prefixEnd_4654542 796672424179877772239719 := by
  unfold tailWord_4654542
  simp only [CollatzResearch.WordTrace]
  refine ⟨21220636687924592666362735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113176729002264494220601253 21220636687924592666362735)
  ·
    refine ⟨31830955031886888999544103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21220636687924592666362735 31830955031886888999544103)
    ·
      refine ⟨47746432547830333499316155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31830955031886888999544103 47746432547830333499316155)
      ·
        refine ⟨71619648821745500248974233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47746432547830333499316155 71619648821745500248974233)
        ·
          refine ⟨53714736616309125186730675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71619648821745500248974233 53714736616309125186730675)
          ·
            refine ⟨80572104924463687780096013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53714736616309125186730675 80572104924463687780096013)
            ·
              refine ⟨30214539346673882917536005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80572104924463687780096013 30214539346673882917536005)
              ·
                refine ⟨5665226127501353047038001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30214539346673882917536005 5665226127501353047038001)
                ·
                  refine ⟨4248919595626014785278501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5665226127501353047038001 4248919595626014785278501)
                  ·
                    refine ⟨796672424179877772239719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4248919595626014785278501 796672424179877772239719)
                    ·
                      rfl

theorem cell23_4654542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 4, 2, 4].length) (baseStart_4654542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4654542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4654542 prefixEnd_4654542 := by exact prefixLift 4654542
  have htrace : WordTrace (prefixWord ++ tailWord_4654542) baseStart_4654542 baseEnd_4654542 := by
    simpa [prefixWord, tailWord_4654542, baseEnd_4654542] using wordTrace_append hprefix tailTrace_4654542
  have hstable : (prefixWord ++ tailWord_4654542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4654542).length < 2 ^ (prefixWord ++ tailWord_4654542).sum := by decide
  have hdescent : baseEnd_4654542 < baseStart_4654542 := by decide
  rcases family_descends (prefixWord ++ tailWord_4654542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4654549 : List Nat := [1, 3, 2, 3, 1, 1, 2, 3, 3, 2, 2]
def baseStart_4654549 : Nat := 118140960795 + 4654549 * 2 ^ 59
def prefixEnd_4654549 : Nat := 4983230072969 + 3 ^ 40 * 4654549 * 2
def baseEnd_4654549 : Nat := 2390020866904214789331625

theorem tailTrace_4654549 : CollatzResearch.WordTrace tailWord_4654549 prefixEnd_4654549 2390020866904214789331625 := by
  unfold tailWord_4654549
  simp only [CollatzResearch.WordTrace]
  refine ⟨169765348814371381526406701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113176899209580921017604467 169765348814371381526406701)
  ·
    refine ⟨63662005805389268072402513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169765348814371381526406701 63662005805389268072402513)
    ·
      refine ⟨47746504354041951054301885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63662005805389268072402513 47746504354041951054301885)
      ·
        refine ⟨17904939132765731645363207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47746504354041951054301885 17904939132765731645363207)
        ·
          refine ⟨26857408699148597468044811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17904939132765731645363207 26857408699148597468044811)
          ·
            refine ⟨40286113048722896202067217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26857408699148597468044811 40286113048722896202067217)
            ·
              refine ⟨30214584786542172151550413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40286113048722896202067217 30214584786542172151550413)
              ·
                refine ⟨11330469294953314556831405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30214584786542172151550413 11330469294953314556831405)
                ·
                  refine ⟨4248925985607492958811777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11330469294953314556831405 4248925985607492958811777)
                  ·
                    refine ⟨3186694489205619719108833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4248925985607492958811777 3186694489205619719108833)
                    ·
                      refine ⟨2390020866904214789331625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3186694489205619719108833 2390020866904214789331625)
                      ·
                        rfl

theorem cell23_4654549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 3, 3, 2, 2].length) (baseStart_4654549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4654549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4654549 prefixEnd_4654549 := by exact prefixLift 4654549
  have htrace : WordTrace (prefixWord ++ tailWord_4654549) baseStart_4654549 baseEnd_4654549 := by
    simpa [prefixWord, tailWord_4654549, baseEnd_4654549] using wordTrace_append hprefix tailTrace_4654549
  have hstable : (prefixWord ++ tailWord_4654549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4654549).length < 2 ^ (prefixWord ++ tailWord_4654549).sum := by decide
  have hdescent : baseEnd_4654549 < baseStart_4654549 := by decide
  rcases family_descends (prefixWord ++ tailWord_4654549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4654599 : List Nat := [1, 1, 4, 3, 2, 2, 1, 1, 4, 1, 3]
def baseStart_4654599 : Nat := 118140960795 + 4654599 * 2 ^ 59
def prefixEnd_4654599 : Nat := 4983230072969 + 3 ^ 40 * 4654599 * 2
def baseEnd_4654599 : Nat := 2390046540936939593706395

theorem tailTrace_4654599 : CollatzResearch.WordTrace tailWord_4654599 prefixEnd_4654599 2390046540936939593706395 := by
  unfold tailWord_4654599
  simp only [CollatzResearch.WordTrace]
  refine ⟨169767172464190240065726851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113178114976126826710484567 169767172464190240065726851)
  ·
    refine ⟨254650758696285360098590277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169767172464190240065726851 254650758696285360098590277)
    ·
      refine ⟨47747017255553505018485677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 254650758696285360098590277 47747017255553505018485677)
      ·
        refine ⟨17905131470832564381932129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47747017255553505018485677 17905131470832564381932129)
        ·
          refine ⟨13428848603124423286449097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17905131470832564381932129 13428848603124423286449097)
          ·
            refine ⟨10071636452343317464836823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13428848603124423286449097 10071636452343317464836823)
            ·
              refine ⟨15107454678514976197255235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10071636452343317464836823 15107454678514976197255235)
              ·
                refine ⟨22661182017772464295882853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15107454678514976197255235 22661182017772464295882853)
                ·
                  refine ⟨4248971628332337055478035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22661182017772464295882853 4248971628332337055478035)
                  ·
                    refine ⟨6373457442498505583217053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4248971628332337055478035 6373457442498505583217053)
                    ·
                      refine ⟨2390046540936939593706395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6373457442498505583217053 2390046540936939593706395)
                      ·
                        rfl

theorem cell23_4654599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_4654599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4654599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4654599 prefixEnd_4654599 := by exact prefixLift 4654599
  have htrace : WordTrace (prefixWord ++ tailWord_4654599) baseStart_4654599 baseEnd_4654599 := by
    simpa [prefixWord, tailWord_4654599, baseEnd_4654599] using wordTrace_append hprefix tailTrace_4654599
  have hstable : (prefixWord ++ tailWord_4654599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4654599).length < 2 ^ (prefixWord ++ tailWord_4654599).sum := by decide
  have hdescent : baseEnd_4654599 < baseStart_4654599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4654599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4654616 : List Nat := [2, 1, 2, 3, 5, 1, 1, 1, 1, 3, 3]
def baseStart_4654616 : Nat := 118140960795 + 4654616 * 2 ^ 59
def prefixEnd_4654616 : Nat := 4983230072969 + 3 ^ 40 * 4654616 * 2
def baseEnd_4654616 : Nat := 2390055270108066027193817

theorem tailTrace_4654616 : CollatzResearch.WordTrace tailWord_4654616 prefixEnd_4654616 2390055270108066027193817 := by
  unfold tailWord_4654616
  simp only [CollatzResearch.WordTrace]
  refine ⟨84883896252564325984547851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113178528336752434646063801 84883896252564325984547851)
  ·
    refine ⟨127325844378846488976821777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84883896252564325984547851 127325844378846488976821777)
    ·
      refine ⟨95494383284134866732616333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127325844378846488976821777 95494383284134866732616333)
      ·
        refine ⟨35810393731550575024731125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95494383284134866732616333 35810393731550575024731125)
        ·
          refine ⟨3357224412332866408568543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35810393731550575024731125 3357224412332866408568543)
          ·
            refine ⟨5035836618499299612852815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3357224412332866408568543 5035836618499299612852815)
            ·
              refine ⟨7553754927748949419279223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5035836618499299612852815 7553754927748949419279223)
              ·
                refine ⟨11330632391623424128918835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7553754927748949419279223 11330632391623424128918835)
                ·
                  refine ⟨16995948587435136193378253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11330632391623424128918835 16995948587435136193378253)
                  ·
                    refine ⟨6373480720288176072516845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16995948587435136193378253 6373480720288176072516845)
                    ·
                      refine ⟨2390055270108066027193817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6373480720288176072516845 2390055270108066027193817)
                      ·
                        rfl

theorem cell23_4654616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 1, 1, 3, 3].length) (baseStart_4654616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4654616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4654616 prefixEnd_4654616 := by exact prefixLift 4654616
  have htrace : WordTrace (prefixWord ++ tailWord_4654616) baseStart_4654616 baseEnd_4654616 := by
    simpa [prefixWord, tailWord_4654616, baseEnd_4654616] using wordTrace_append hprefix tailTrace_4654616
  have hstable : (prefixWord ++ tailWord_4654616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4654616).length < 2 ^ (prefixWord ++ tailWord_4654616).sum := by decide
  have hdescent : baseEnd_4654616 < baseStart_4654616 := by decide
  rcases family_descends (prefixWord ++ tailWord_4654616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4654692 : List Nat := [2, 3, 1, 1, 2, 3, 1, 3, 2, 5]
def baseStart_4654692 : Nat := 118140960795 + 4654692 * 2 ^ 59
def prefixEnd_4654692 : Nat := 4983230072969 + 3 ^ 40 * 4654692 * 2
def baseEnd_4654692 : Nat := 796698098212602576614489

theorem tailTrace_4654692 : CollatzResearch.WordTrace tailWord_4654692 prefixEnd_4654692 796698098212602576614489 := by
  unfold tailWord_4654692
  simp only [CollatzResearch.WordTrace]
  refine ⟨84885282226426658474431165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113180376301902211299241553 84885282226426658474431165)
  ·
    refine ⟨31831980834909996927911687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84885282226426658474431165 31831980834909996927911687)
    ·
      refine ⟨47747971252364995391867531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31831980834909996927911687 47747971252364995391867531)
      ·
        refine ⟨71621956878547493087801297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47747971252364995391867531 71621956878547493087801297)
        ·
          refine ⟨53716467658910619815850973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71621956878547493087801297 53716467658910619815850973)
          ·
            refine ⟨20143675372091482430944115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53716467658910619815850973 20143675372091482430944115)
            ·
              refine ⟨30215513058137223646416173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20143675372091482430944115 30215513058137223646416173)
              ·
                refine ⟨11330817396801458867406065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30215513058137223646416173 11330817396801458867406065)
                ·
                  refine ⟨8498113047601094150554549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11330817396801458867406065 8498113047601094150554549)
                  ·
                    refine ⟨796698098212602576614489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8498113047601094150554549 796698098212602576614489)
                    ·
                      rfl

theorem cell23_4654692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 3, 2, 5].length) (baseStart_4654692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4654692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4654692 prefixEnd_4654692 := by exact prefixLift 4654692
  have htrace : WordTrace (prefixWord ++ tailWord_4654692) baseStart_4654692 baseEnd_4654692 := by
    simpa [prefixWord, tailWord_4654692, baseEnd_4654692] using wordTrace_append hprefix tailTrace_4654692
  have hstable : (prefixWord ++ tailWord_4654692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4654692).length < 2 ^ (prefixWord ++ tailWord_4654692).sum := by decide
  have hdescent : baseEnd_4654692 < baseStart_4654692 := by decide
  rcases family_descends (prefixWord ++ tailWord_4654692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4654709 : List Nat := [1, 3, 4, 2, 1, 1, 2, 2, 2, 5]
def baseStart_4654709 : Nat := 118140960795 + 4654709 * 2 ^ 59
def prefixEnd_4654709 : Nat := 4983230072969 + 3 ^ 40 * 4654709 * 2
def baseEnd_4654709 : Nat := 796701007936311387776963

theorem tailTrace_4654709 : CollatzResearch.WordTrace tailWord_4654709 prefixEnd_4654709 796701007936311387776963 := by
  unfold tailWord_4654709
  simp only [CollatzResearch.WordTrace]
  refine ⟨169771184493791728852231181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113180789662527819234820787 169771184493791728852231181)
  ·
    refine ⟨63664194185171898319586693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169771184493791728852231181 63664194185171898319586693)
    ·
      refine ⟨11937036409719730934922505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63664194185171898319586693 11937036409719730934922505)
      ·
        refine ⟨8952777307289798201191879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11937036409719730934922505 8952777307289798201191879)
        ·
          refine ⟨13429165960934697301787819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8952777307289798201191879 13429165960934697301787819)
          ·
            refine ⟨20143748941402045952681729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13429165960934697301787819 20143748941402045952681729)
            ·
              refine ⟨15107811706051534464511297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20143748941402045952681729 15107811706051534464511297)
              ·
                refine ⟨11330858779538650848383473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15107811706051534464511297 11330858779538650848383473)
                ·
                  refine ⟨8498144084653988136287605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11330858779538650848383473 8498144084653988136287605)
                  ·
                    refine ⟨796701007936311387776963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8498144084653988136287605 796701007936311387776963)
                    ·
                      rfl

theorem cell23_4654709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_4654709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4654709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4654709 prefixEnd_4654709 := by exact prefixLift 4654709
  have htrace : WordTrace (prefixWord ++ tailWord_4654709) baseStart_4654709 baseEnd_4654709 := by
    simpa [prefixWord, tailWord_4654709, baseEnd_4654709] using wordTrace_append hprefix tailTrace_4654709
  have hstable : (prefixWord ++ tailWord_4654709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4654709).length < 2 ^ (prefixWord ++ tailWord_4654709).sum := by decide
  have hdescent : baseEnd_4654709 < baseStart_4654709 := by decide
  rcases family_descends (prefixWord ++ tailWord_4654709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4654715 : List Nat := [1, 1, 1, 1, 1, 4, 3, 1, 2, 3, 5]
def baseStart_4654715 : Nat := 118140960795 + 4654715 * 2 ^ 59
def prefixEnd_4654715 : Nat := 4983230072969 + 3 ^ 40 * 4654715 * 2
def baseEnd_4654715 : Nat := 2390106104692861139855861

theorem tailTrace_4654715 : CollatzResearch.WordTrace tailWord_4654715 prefixEnd_4654715 2390106104692861139855861 := by
  unfold tailWord_4654715
  simp only [CollatzResearch.WordTrace]
  refine ⟨169771403331769991876949599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113180935554513327917966399 169771403331769991876949599)
  ·
    refine ⟨254657104997654987815424399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169771403331769991876949599 254657104997654987815424399)
    ·
      refine ⟨381985657496482481723136599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254657104997654987815424399 381985657496482481723136599)
      ·
        refine ⟨572978486244723722584704899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 381985657496482481723136599 572978486244723722584704899)
        ·
          refine ⟨859467729367085583877057349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 572978486244723722584704899 859467729367085583877057349)
          ·
            refine ⟨161150199256328546976948253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 859467729367085583877057349 161150199256328546976948253)
            ·
              refine ⟨60431324721123205116355595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 161150199256328546976948253 60431324721123205116355595)
              ·
                refine ⟨90646987081684807674533393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60431324721123205116355595 90646987081684807674533393)
                ·
                  refine ⟨67985240311263605755900045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90646987081684807674533393 67985240311263605755900045)
                  ·
                    refine ⟨25494465116723852158462517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 67985240311263605755900045 25494465116723852158462517)
                    ·
                      refine ⟨2390106104692861139855861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25494465116723852158462517 2390106104692861139855861)
                      ·
                        rfl

theorem cell23_4654715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 3, 5].length) (baseStart_4654715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4654715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4654715 prefixEnd_4654715 := by exact prefixLift 4654715
  have htrace : WordTrace (prefixWord ++ tailWord_4654715) baseStart_4654715 baseEnd_4654715 := by
    simpa [prefixWord, tailWord_4654715, baseEnd_4654715] using wordTrace_append hprefix tailTrace_4654715
  have hstable : (prefixWord ++ tailWord_4654715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4654715).length < 2 ^ (prefixWord ++ tailWord_4654715).sum := by decide
  have hdescent : baseEnd_4654715 < baseStart_4654715 := by decide
  rcases family_descends (prefixWord ++ tailWord_4654715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4654732 : List Nat := [2, 2, 1, 2, 1, 1, 4, 2, 1, 4, 3]
def baseStart_4654732 : Nat := 118140960795 + 4654732 * 2 ^ 59
def prefixEnd_4654732 : Nat := 4983230072969 + 3 ^ 40 * 4654732 * 2
def baseEnd_4654732 : Nat := 2390114833863987573343283

theorem tailTrace_4654732 : CollatzResearch.WordTrace tailWord_4654732 prefixEnd_4654732 2390114833863987573343283 := by
  unfold tailWord_4654732
  simp only [CollatzResearch.WordTrace]
  refine ⟨84886011686354201890159225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113181348915138935853545633 84886011686354201890159225)
  ·
    refine ⟨63664508764765651417619419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84886011686354201890159225 63664508764765651417619419)
    ·
      refine ⟨95496763147148477126429129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63664508764765651417619419 95496763147148477126429129)
      ·
        refine ⟨71622572360361357844821847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95496763147148477126429129 71622572360361357844821847)
        ·
          refine ⟨107433858540542036767232771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71622572360361357844821847 107433858540542036767232771)
          ·
            refine ⟨161150787810813055150849157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107433858540542036767232771 161150787810813055150849157)
            ·
              refine ⟨30215772714527447840784217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 161150787810813055150849157 30215772714527447840784217)
              ·
                refine ⟨22661829535895585880588163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30215772714527447840784217 22661829535895585880588163)
                ·
                  refine ⟨33992744303843378820882245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22661829535895585880588163 33992744303843378820882245)
                  ·
                    refine ⟨6373639556970633528915421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33992744303843378820882245 6373639556970633528915421)
                    ·
                      refine ⟨2390114833863987573343283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6373639556970633528915421 2390114833863987573343283)
                      ·
                        rfl

theorem cell23_4654732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 1, 4, 3].length) (baseStart_4654732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4654732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4654732 prefixEnd_4654732 := by exact prefixLift 4654732
  have htrace : WordTrace (prefixWord ++ tailWord_4654732) baseStart_4654732 baseEnd_4654732 := by
    simpa [prefixWord, tailWord_4654732, baseEnd_4654732] using wordTrace_append hprefix tailTrace_4654732
  have hstable : (prefixWord ++ tailWord_4654732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4654732).length < 2 ^ (prefixWord ++ tailWord_4654732).sum := by decide
  have hdescent : baseEnd_4654732 < baseStart_4654732 := by decide
  rcases family_descends (prefixWord ++ tailWord_4654732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4654756 : List Nat := [2, 3, 1, 2, 2, 2, 1, 5, 1, 4]
def baseStart_4654756 : Nat := 118140960795 + 4654756 * 2 ^ 59
def prefixEnd_4654756 : Nat := 4983230072969 + 3 ^ 40 * 4654756 * 2
def baseEnd_4654756 : Nat := 796709052466565159814391

theorem tailTrace_4654756 : CollatzResearch.WordTrace tailWord_4654756 prefixEnd_4654756 796709052466565159814391 := by
  unfold tailWord_4654756
  simp only [CollatzResearch.WordTrace]
  refine ⟨84886449362310727939596061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113181932483080970586128081 84886449362310727939596061)
  ·
    refine ⟨31832418510866522977348523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84886449362310727939596061 31832418510866522977348523)
    ·
      refine ⟨47748627766299784466022785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31832418510866522977348523 47748627766299784466022785)
      ·
        refine ⟨35811470824724838349517089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47748627766299784466022785 35811470824724838349517089)
        ·
          refine ⟨26858603118543628762137817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35811470824724838349517089 26858603118543628762137817)
          ·
            refine ⟨20143952338907721571603363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26858603118543628762137817 20143952338907721571603363)
            ·
              refine ⟨30215928508361582357405045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20143952338907721571603363 30215928508361582357405045)
              ·
                refine ⟨2832743297658898346006723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30215928508361582357405045 2832743297658898346006723)
                ·
                  refine ⟨4249114946488347519010085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2832743297658898346006723 4249114946488347519010085)
                  ·
                    refine ⟨796709052466565159814391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4249114946488347519010085 796709052466565159814391)
                    ·
                      rfl

theorem cell23_4654756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 5, 1, 4].length) (baseStart_4654756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4654756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4654756 prefixEnd_4654756 := by exact prefixLift 4654756
  have htrace : WordTrace (prefixWord ++ tailWord_4654756) baseStart_4654756 baseEnd_4654756 := by
    simpa [prefixWord, tailWord_4654756, baseEnd_4654756] using wordTrace_append hprefix tailTrace_4654756
  have hstable : (prefixWord ++ tailWord_4654756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4654756).length < 2 ^ (prefixWord ++ tailWord_4654756).sum := by decide
  have hdescent : baseEnd_4654756 < baseStart_4654756 := by decide
  rcases family_descends (prefixWord ++ tailWord_4654756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4654789 : List Nat := [1, 3, 1, 1, 1, 1, 2, 4, 4, 3, 2]
def baseStart_4654789 : Nat := 118140960795 + 4654789 * 2 ^ 59
def prefixEnd_4654789 : Nat := 4983230072969 + 3 ^ 40 * 4654789 * 2
def baseEnd_4654789 : Nat := 2390144102261293850330521

theorem tailTrace_4654789 : CollatzResearch.WordTrace tailWord_4654789 prefixEnd_4654789 2390144102261293850330521 := by
  unfold tailWord_4654789
  simp only [CollatzResearch.WordTrace]
  refine ⟨169774102333501902515143421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113182734889001268343428947 169774102333501902515143421)
  ·
    refine ⟨63665288375063213443178783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169774102333501902515143421 63665288375063213443178783)
    ·
      refine ⟨95497932562594820164768175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63665288375063213443178783 95497932562594820164768175)
      ·
        refine ⟨143246898843892230247152263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95497932562594820164768175 143246898843892230247152263)
        ·
          refine ⟨214870348265838345370728395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143246898843892230247152263 214870348265838345370728395)
          ·
            refine ⟨322305522398757518056092593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214870348265838345370728395 322305522398757518056092593)
            ·
              refine ⟨241729141799068138542069445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 322305522398757518056092593 241729141799068138542069445)
              ·
                refine ⟨45324214087325275976638021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 241729141799068138542069445 45324214087325275976638021)
                ·
                  refine ⟨8498290141373489245619629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45324214087325275976638021 8498290141373489245619629)
                  ·
                    refine ⟨3186858803015058467107361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8498290141373489245619629 3186858803015058467107361)
                    ·
                      refine ⟨2390144102261293850330521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3186858803015058467107361 2390144102261293850330521)
                      ·
                        rfl

theorem cell23_4654789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 4, 3, 2].length) (baseStart_4654789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4654789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4654789 prefixEnd_4654789 := by exact prefixLift 4654789
  have htrace : WordTrace (prefixWord ++ tailWord_4654789) baseStart_4654789 baseEnd_4654789 := by
    simpa [prefixWord, tailWord_4654789, baseEnd_4654789] using wordTrace_append hprefix tailTrace_4654789
  have hstable : (prefixWord ++ tailWord_4654789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4654789).length < 2 ^ (prefixWord ++ tailWord_4654789).sum := by decide
  have hdescent : baseEnd_4654789 < baseStart_4654789 := by decide
  rcases family_descends (prefixWord ++ tailWord_4654789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4654830 : List Nat := [4, 1, 2, 1, 1, 2, 5, 2, 1, 1, 3]
def baseStart_4654830 : Nat := 118140960795 + 4654830 * 2 ^ 59
def prefixEnd_4654830 : Nat := 4983230072969 + 3 ^ 40 * 4654830 * 2
def baseEnd_4654830 : Nat := 2390165154968128189917833

theorem tailTrace_4654830 : CollatzResearch.WordTrace tailWord_4654830 prefixEnd_4654830 2390165154968128189917833 := by
  unfold tailWord_4654830
  simp only [CollatzResearch.WordTrace]
  refine ⟨21221949715794170814673243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113183731817568911011590629 21221949715794170814673243)
  ·
    refine ⟨31832924573691256222009865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21221949715794170814673243 31832924573691256222009865)
    ·
      refine ⟨23874693430268442166507399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31832924573691256222009865 23874693430268442166507399)
      ·
        refine ⟨35812040145402663249761099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23874693430268442166507399 35812040145402663249761099)
        ·
          refine ⟨53718060218103994874641649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35812040145402663249761099 53718060218103994874641649)
          ·
            refine ⟨40288545163577996155981237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53718060218103994874641649 40288545163577996155981237)
            ·
              refine ⟨3777051109085437139623241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40288545163577996155981237 3777051109085437139623241)
              ·
                refine ⟨2832788331814077854717431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3777051109085437139623241 2832788331814077854717431)
                ·
                  refine ⟨4249182497721116782076147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2832788331814077854717431 4249182497721116782076147)
                  ·
                    refine ⟨6373773746581675173114221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4249182497721116782076147 6373773746581675173114221)
                    ·
                      refine ⟨2390165154968128189917833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6373773746581675173114221 2390165154968128189917833)
                      ·
                        rfl

theorem cell23_4654830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 5, 2, 1, 1, 3].length) (baseStart_4654830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4654830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4654830 prefixEnd_4654830 := by exact prefixLift 4654830
  have htrace : WordTrace (prefixWord ++ tailWord_4654830) baseStart_4654830 baseEnd_4654830 := by
    simpa [prefixWord, tailWord_4654830, baseEnd_4654830] using wordTrace_append hprefix tailTrace_4654830
  have hstable : (prefixWord ++ tailWord_4654830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4654830).length < 2 ^ (prefixWord ++ tailWord_4654830).sum := by decide
  have hdescent : baseEnd_4654830 < baseStart_4654830 := by decide
  rcases family_descends (prefixWord ++ tailWord_4654830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4654832 : List Nat := [2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 4]
def baseStart_4654832 : Nat := 118140960795 + 4654832 * 2 ^ 59
def prefixEnd_4654832 : Nat := 4983230072969 + 3 ^ 40 * 4654832 * 2
def baseEnd_4654832 : Nat := 2390166181929437182092823

theorem tailTrace_4654832 : CollatzResearch.WordTrace tailWord_4654832 prefixEnd_4654832 2390166181929437182092823 := by
  unfold tailWord_4654832
  simp only [CollatzResearch.WordTrace]
  refine ⟨84887835336173060429479375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113183780448230747239305833 84887835336173060429479375)
  ·
    refine ⟨127331753004259590644219063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84887835336173060429479375 127331753004259590644219063)
    ·
      refine ⟨190997629506389385966328595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127331753004259590644219063 190997629506389385966328595)
      ·
        refine ⟨286496444259584078949492893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190997629506389385966328595 286496444259584078949492893)
        ·
          refine ⟨107436166597344029606059835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 286496444259584078949492893 107436166597344029606059835)
          ·
            refine ⟨161154249896016044409089753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107436166597344029606059835 161154249896016044409089753)
            ·
              refine ⟨120865687422012033306817315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 161154249896016044409089753 120865687422012033306817315)
              ·
                refine ⟨181298531133018049960225973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120865687422012033306817315 181298531133018049960225973)
                ·
                  refine ⟨16996737293720442183771185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 181298531133018049960225973 16996737293720442183771185)
                  ·
                    refine ⟨12747552970290331637828389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16996737293720442183771185 12747552970290331637828389)
                    ·
                      refine ⟨2390166181929437182092823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12747552970290331637828389 2390166181929437182092823)
                      ·
                        rfl

theorem cell23_4654832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 4].length) (baseStart_4654832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4654832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4654832 prefixEnd_4654832 := by exact prefixLift 4654832
  have htrace : WordTrace (prefixWord ++ tailWord_4654832) baseStart_4654832 baseEnd_4654832 := by
    simpa [prefixWord, tailWord_4654832, baseEnd_4654832] using wordTrace_append hprefix tailTrace_4654832
  have hstable : (prefixWord ++ tailWord_4654832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4654832).length < 2 ^ (prefixWord ++ tailWord_4654832).sum := by decide
  have hdescent : baseEnd_4654832 < baseStart_4654832 := by decide
  rcases family_descends (prefixWord ++ tailWord_4654832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4654866 : List Nat := [3, 2, 4, 1, 1, 1, 1, 1, 3, 2, 4]
def baseStart_4654866 : Nat := 118140960795 + 4654866 * 2 ^ 59
def prefixEnd_4654866 : Nat := 4983230072969 + 3 ^ 40 * 4654866 * 2
def baseEnd_4654866 : Nat := 2390183640271690049067667

theorem tailTrace_4654866 : CollatzResearch.WordTrace tailWord_4654866 prefixEnd_4654866 2390183640271690049067667 := by
  unfold tailWord_4654866
  simp only [CollatzResearch.WordTrace]
  refine ⟨42444227688555736166424113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113184607169481963110464301 42444227688555736166424113)
  ·
    refine ⟨31833170766416802124818085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42444227688555736166424113 31833170766416802124818085)
    ·
      refine ⟨5968719518703150398403391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31833170766416802124818085 5968719518703150398403391)
      ·
        refine ⟨8953079278054725597605087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5968719518703150398403391 8953079278054725597605087)
        ·
          refine ⟨13429618917082088396407631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8953079278054725597605087 13429618917082088396407631)
          ·
            refine ⟨20144428375623132594611447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13429618917082088396407631 20144428375623132594611447)
            ·
              refine ⟨30216642563434698891917171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20144428375623132594611447 30216642563434698891917171)
              ·
                refine ⟨45324963845152048337875757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30216642563434698891917171 45324963845152048337875757)
                ·
                  refine ⟨16996861441932018126703409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45324963845152048337875757 16996861441932018126703409)
                  ·
                    refine ⟨12747646081449013595027557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16996861441932018126703409 12747646081449013595027557)
                    ·
                      refine ⟨2390183640271690049067667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12747646081449013595027557 2390183640271690049067667)
                      ·
                        rfl

theorem cell23_4654866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_4654866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4654866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4654866 prefixEnd_4654866 := by exact prefixLift 4654866
  have htrace : WordTrace (prefixWord ++ tailWord_4654866) baseStart_4654866 baseEnd_4654866 := by
    simpa [prefixWord, tailWord_4654866, baseEnd_4654866] using wordTrace_append hprefix tailTrace_4654866
  have hstable : (prefixWord ++ tailWord_4654866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4654866).length < 2 ^ (prefixWord ++ tailWord_4654866).sum := by decide
  have hdescent : baseEnd_4654866 < baseStart_4654866 := by decide
  rcases family_descends (prefixWord ++ tailWord_4654866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4654869 : List Nat := [1, 3, 2, 1, 2, 3, 1, 1, 3, 3, 3]
def baseStart_4654869 : Nat := 118140960795 + 4654869 * 2 ^ 59
def prefixEnd_4654869 : Nat := 4983230072969 + 3 ^ 40 * 4654869 * 2
def baseEnd_4654869 : Nat := 2390185180713653537330153

theorem tailTrace_4654869 : CollatzResearch.WordTrace tailWord_4654869 prefixEnd_4654869 2390185180713653537330153 := by
  unfold tailWord_4654869
  simp only [CollatzResearch.WordTrace]
  refine ⟨169777020173212076178055661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113184680115474717452037107 169777020173212076178055661)
  ·
    refine ⟨63666382564954528566770873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169777020173212076178055661 63666382564954528566770873)
    ·
      refine ⟨47749786923715896425078155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63666382564954528566770873 47749786923715896425078155)
      ·
        refine ⟨71624680385573844637617233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47749786923715896425078155 71624680385573844637617233)
        ·
          refine ⟨53718510289180383478212925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71624680385573844637617233 53718510289180383478212925)
          ·
            refine ⟨20144441358442643804329847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53718510289180383478212925 20144441358442643804329847)
            ·
              refine ⟨30216662037663965706494771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20144441358442643804329847 30216662037663965706494771)
              ·
                refine ⟨45324993056495948559742157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30216662037663965706494771 45324993056495948559742157)
                ·
                  refine ⟨16996872396185980709903309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45324993056495948559742157 16996872396185980709903309)
                  ·
                    refine ⟨6373827148569742766213741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16996872396185980709903309 6373827148569742766213741)
                    ·
                      refine ⟨2390185180713653537330153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6373827148569742766213741 2390185180713653537330153)
                      ·
                        rfl

theorem cell23_4654869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 3, 3, 3].length) (baseStart_4654869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4654869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4654869 prefixEnd_4654869 := by exact prefixLift 4654869
  have htrace : WordTrace (prefixWord ++ tailWord_4654869) baseStart_4654869 baseEnd_4654869 := by
    simpa [prefixWord, tailWord_4654869, baseEnd_4654869] using wordTrace_append hprefix tailTrace_4654869
  have hstable : (prefixWord ++ tailWord_4654869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4654869).length < 2 ^ (prefixWord ++ tailWord_4654869).sum := by decide
  have hdescent : baseEnd_4654869 < baseStart_4654869 := by decide
  rcases family_descends (prefixWord ++ tailWord_4654869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4654930 : List Nat := [3, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2]
def baseStart_4654930 : Nat := 118140960795 + 4654930 * 2 ^ 59
def prefixEnd_4654930 : Nat := 4983230072969 + 3 ^ 40 * 4654930 * 2
def baseEnd_4654930 : Nat := 2390216503033577798667373

theorem tailTrace_4654930 : CollatzResearch.WordTrace tailWord_4654930 prefixEnd_4654930 2390216503033577798667373 := by
  unfold tailWord_4654930
  simp only [CollatzResearch.WordTrace]
  refine ⟨42444811256497770899006561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113186163350660722397350829 42444811256497770899006561)
  ·
    refine ⟨31833608442373328174254921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42444811256497770899006561 31833608442373328174254921)
    ·
      refine ⟨23875206331779996130691191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31833608442373328174254921 23875206331779996130691191)
      ·
        refine ⟨35812809497669994196036787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23875206331779996130691191 35812809497669994196036787)
        ·
          refine ⟨53719214246504991294055181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35812809497669994196036787 53719214246504991294055181)
          ·
            refine ⟨20144705342439371735270693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53719214246504991294055181 20144705342439371735270693)
            ·
              refine ⟨3777132251707382200363255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20144705342439371735270693 3777132251707382200363255)
              ·
                refine ⟨5665698377561073300544883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3777132251707382200363255 5665698377561073300544883)
                ·
                  refine ⟨8498547566341609950817325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5665698377561073300544883 8498547566341609950817325)
                  ·
                    refine ⟨3186955337378103731556497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8498547566341609950817325 3186955337378103731556497)
                    ·
                      refine ⟨2390216503033577798667373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3186955337378103731556497 2390216503033577798667373)
                      ·
                        rfl

theorem cell23_4654930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2].length) (baseStart_4654930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4654930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4654930 prefixEnd_4654930 := by exact prefixLift 4654930
  have htrace : WordTrace (prefixWord ++ tailWord_4654930) baseStart_4654930 baseEnd_4654930 := by
    simpa [prefixWord, tailWord_4654930, baseEnd_4654930] using wordTrace_append hprefix tailTrace_4654930
  have hstable : (prefixWord ++ tailWord_4654930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4654930).length < 2 ^ (prefixWord ++ tailWord_4654930).sum := by decide
  have hdescent : baseEnd_4654930 < baseStart_4654930 := by decide
  rcases family_descends (prefixWord ++ tailWord_4654930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4654943 : List Nat := [1, 1, 2, 3, 1, 5, 1, 1, 4, 2, 2]
def baseStart_4654943 : Nat := 118140960795 + 4654943 * 2 ^ 59
def prefixEnd_4654943 : Nat := 4983230072969 + 3 ^ 40 * 4654943 * 2
def baseEnd_4654943 : Nat := 2390223178282086247804813

theorem tailTrace_4654943 : CollatzResearch.WordTrace tailWord_4654943 prefixEnd_4654943 2390223178282086247804813 := by
  unfold tailWord_4654943
  simp only [CollatzResearch.WordTrace]
  refine ⟨169779719174943986816249483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113186479449962657877499655 169779719174943986816249483)
  ·
    refine ⟨254669578762415980224374225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169779719174943986816249483 254669578762415980224374225)
    ·
      refine ⟨191002184071811985168280669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 254669578762415980224374225 191002184071811985168280669)
      ·
        refine ⟨71625819026929494438105251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 191002184071811985168280669 71625819026929494438105251)
        ·
          refine ⟨107438728540394241657157877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71625819026929494438105251 107438728540394241657157877)
          ·
            refine ⟨10072380800661960155358551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 107438728540394241657157877 10072380800661960155358551)
            ·
              refine ⟨15108571200992940233037827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10072380800661960155358551 15108571200992940233037827)
              ·
                refine ⟨22662856801489410349556741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15108571200992940233037827 22662856801489410349556741)
                ·
                  refine ⟨4249285650279264440541889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22662856801489410349556741 4249285650279264440541889)
                  ·
                    refine ⟨3186964237709448330406417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4249285650279264440541889 3186964237709448330406417)
                    ·
                      refine ⟨2390223178282086247804813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3186964237709448330406417 2390223178282086247804813)
                      ·
                        rfl

theorem cell23_4654943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 4, 2, 2].length) (baseStart_4654943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4654943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4654943 prefixEnd_4654943 := by exact prefixLift 4654943
  have htrace : WordTrace (prefixWord ++ tailWord_4654943) baseStart_4654943 baseEnd_4654943 := by
    simpa [prefixWord, tailWord_4654943, baseEnd_4654943] using wordTrace_append hprefix tailTrace_4654943
  have hstable : (prefixWord ++ tailWord_4654943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4654943).length < 2 ^ (prefixWord ++ tailWord_4654943).sum := by decide
  have hdescent : baseEnd_4654943 < baseStart_4654943 := by decide
  rcases family_descends (prefixWord ++ tailWord_4654943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4654979 : List Nat := [1, 1, 1, 3, 4, 2, 2, 1, 1, 7]
def baseStart_4654979 : Nat := 118140960795 + 4654979 * 2 ^ 59
def prefixEnd_4654979 : Nat := 4983230072969 + 3 ^ 40 * 4654979 * 2
def baseEnd_4654979 : Nat := 796747221195216035651549

theorem tailTrace_4654979 : CollatzResearch.WordTrace tailWord_4654979 prefixEnd_4654979 796747221195216035651549 := by
  unfold tailWord_4654979
  simp only [CollatzResearch.WordTrace]
  refine ⟨169781032202813564964559991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113187354801875709976373327 169781032202813564964559991)
  ·
    refine ⟨254671548304220347446839987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169781032202813564964559991 254671548304220347446839987)
    ·
      refine ⟨382007322456330521170259981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254671548304220347446839987 382007322456330521170259981)
      ·
        refine ⟨143252745921123945438847493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 382007322456330521170259981 143252745921123945438847493)
        ·
          refine ⟨26859889860210739769783905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 143252745921123945438847493 26859889860210739769783905)
          ·
            refine ⟨20144917395158054827337929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26859889860210739769783905 20144917395158054827337929)
            ·
              refine ⟨15108688046368541120503447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20144917395158054827337929 15108688046368541120503447)
              ·
                refine ⟨22663032069552811680755171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15108688046368541120503447 22663032069552811680755171)
                ·
                  refine ⟨33994548104329217521132757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22663032069552811680755171 33994548104329217521132757)
                  ·
                    refine ⟨796747221195216035651549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33994548104329217521132757 796747221195216035651549)
                    ·
                      rfl

theorem cell23_4654979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 7].length) (baseStart_4654979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4654979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4654979 prefixEnd_4654979 := by exact prefixLift 4654979
  have htrace : WordTrace (prefixWord ++ tailWord_4654979) baseStart_4654979 baseEnd_4654979 := by
    simpa [prefixWord, tailWord_4654979, baseEnd_4654979] using wordTrace_append hprefix tailTrace_4654979
  have hstable : (prefixWord ++ tailWord_4654979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4654979).length < 2 ^ (prefixWord ++ tailWord_4654979).sum := by decide
  have hdescent : baseEnd_4654979 < baseStart_4654979 := by decide
  rcases family_descends (prefixWord ++ tailWord_4654979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4654996 : List Nat := [2, 4, 2, 1, 1, 2, 1, 1, 4, 5]
def baseStart_4654996 : Nat := 118140960795 + 4654996 * 2 ^ 59
def prefixEnd_4654996 : Nat := 4983230072969 + 3 ^ 40 * 4654996 * 2
def baseEnd_4654996 : Nat := 796750130918924846814023

theorem tailTrace_4654996 : CollatzResearch.WordTrace tailWord_4654996 prefixEnd_4654996 796750130918924846814023 := by
  unfold tailWord_4654996
  simp only [CollatzResearch.WordTrace]
  refine ⟨84890826121875988433964421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113187768162501317911952561 84890826121875988433964421)
  ·
    refine ⟨15917029897851747831368329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84890826121875988433964421 15917029897851747831368329)
    ·
      refine ⟨11937772423388810873526247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15917029897851747831368329 11937772423388810873526247)
      ·
        refine ⟨17906658635083216310289371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11937772423388810873526247 17906658635083216310289371)
        ·
          refine ⟨26859987952624824465434057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17906658635083216310289371 26859987952624824465434057)
          ·
            refine ⟨20144990964468618349075543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26859987952624824465434057 20144990964468618349075543)
            ·
              refine ⟨30217486446702927523613315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20144990964468618349075543 30217486446702927523613315)
              ·
                refine ⟨45326229670054391285419973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30217486446702927523613315 45326229670054391285419973)
                ·
                  refine ⟨8498668063135198366016245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45326229670054391285419973 8498668063135198366016245)
                  ·
                    refine ⟨796750130918924846814023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8498668063135198366016245 796750130918924846814023)
                    ·
                      rfl

theorem cell23_4654996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_4654996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4654996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4654996 prefixEnd_4654996 := by exact prefixLift 4654996
  have htrace : WordTrace (prefixWord ++ tailWord_4654996) baseStart_4654996 baseEnd_4654996 := by
    simpa [prefixWord, tailWord_4654996, baseEnd_4654996] using wordTrace_append hprefix tailTrace_4654996
  have hstable : (prefixWord ++ tailWord_4654996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4654996).length < 2 ^ (prefixWord ++ tailWord_4654996).sum := by decide
  have hdescent : baseEnd_4654996 < baseStart_4654996 := by decide
  rcases family_descends (prefixWord ++ tailWord_4654996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4655000 : List Nat := [2, 1, 2, 6, 2, 1, 1, 1, 7]
def baseStart_4655000 : Nat := 118140960795 + 4655000 * 2 ^ 59
def prefixEnd_4655000 : Nat := 4983230072969 + 3 ^ 40 * 4655000 * 2
def baseEnd_4655000 : Nat := 265583605186599169421339

theorem tailTrace_4655000 : CollatzResearch.WordTrace tailWord_4655000 prefixEnd_4655000 265583605186599169421339 := by
  unfold tailWord_4655000
  simp only [CollatzResearch.WordTrace]
  refine ⟨84890899067868742775537227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113187865423824990367382969 84890899067868742775537227)
  ·
    refine ⟨127336348601803114163305841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84890899067868742775537227 127336348601803114163305841)
    ·
      refine ⟨95502261451352335622479381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127336348601803114163305841 95502261451352335622479381)
      ·
        refine ⟨4476668505532140732303721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 95502261451352335622479381 4476668505532140732303721)
        ·
          refine ⟨3357501379149105549227791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4476668505532140732303721 3357501379149105549227791)
          ·
            refine ⟨5036252068723658323841687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3357501379149105549227791 5036252068723658323841687)
            ·
              refine ⟨7554378103085487485762531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5036252068723658323841687 7554378103085487485762531)
              ·
                refine ⟨11331567154628231228643797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7554378103085487485762531 11331567154628231228643797)
                ·
                  refine ⟨265583605186599169421339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11331567154628231228643797 265583605186599169421339)
                  ·
                    rfl

theorem cell23_4655000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 1, 7].length) (baseStart_4655000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4655000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4655000 prefixEnd_4655000 := by exact prefixLift 4655000
  have htrace : WordTrace (prefixWord ++ tailWord_4655000) baseStart_4655000 baseEnd_4655000 := by
    simpa [prefixWord, tailWord_4655000, baseEnd_4655000] using wordTrace_append hprefix tailTrace_4655000
  have hstable : (prefixWord ++ tailWord_4655000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4655000).length < 2 ^ (prefixWord ++ tailWord_4655000).sum := by decide
  have hdescent : baseEnd_4655000 < baseStart_4655000 := by decide
  rcases family_descends (prefixWord ++ tailWord_4655000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4655026 : List Nat := [3, 2, 1, 1, 1, 1, 1, 6, 3, 4]
def baseStart_4655026 : Nat := 118140960795 + 4655026 * 2 ^ 59
def prefixEnd_4655026 : Nat := 4983230072969 + 3 ^ 40 * 4655026 * 2
def baseEnd_4655026 : Nat := 796755265725469807688977

theorem tailTrace_4655026 : CollatzResearch.WordTrace tailWord_4655026 prefixEnd_4655026 796755265725469807688977 := by
  unfold tailWord_4655026
  simp only [CollatzResearch.WordTrace]
  refine ⟨42445686608410822997880233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113188497622428861327680621 42445686608410822997880233)
  ·
    refine ⟨31834264956308117248410175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42445686608410822997880233 31834264956308117248410175)
    ·
      refine ⟨47751397434462175872615263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31834264956308117248410175 47751397434462175872615263)
      ·
        refine ⟨71627096151693263808922895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47751397434462175872615263 71627096151693263808922895)
        ·
          refine ⟨107440644227539895713384343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71627096151693263808922895 107440644227539895713384343)
          ·
            refine ⟨161160966341309843570076515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107440644227539895713384343 161160966341309843570076515)
            ·
              refine ⟨241741449511964765355114773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161160966341309843570076515 241741449511964765355114773)
              ·
                refine ⟨11331630445873348376021005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 241741449511964765355114773 11331630445873348376021005)
                ·
                  refine ⟨4249361417202505641007877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11331630445873348376021005 4249361417202505641007877)
                  ·
                    refine ⟨796755265725469807688977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4249361417202505641007877 796755265725469807688977)
                    ·
                      rfl

theorem cell23_4655026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 6, 3, 4].length) (baseStart_4655026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4655026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4655026 prefixEnd_4655026 := by exact prefixLift 4655026
  have htrace : WordTrace (prefixWord ++ tailWord_4655026) baseStart_4655026 baseEnd_4655026 := by
    simpa [prefixWord, tailWord_4655026, baseEnd_4655026] using wordTrace_append hprefix tailTrace_4655026
  have hstable : (prefixWord ++ tailWord_4655026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4655026).length < 2 ^ (prefixWord ++ tailWord_4655026).sum := by decide
  have hdescent : baseEnd_4655026 < baseStart_4655026 := by decide
  rcases family_descends (prefixWord ++ tailWord_4655026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4655060 : List Nat := [2, 4, 1, 2, 1, 1, 3, 4, 1, 4]
def baseStart_4655060 : Nat := 118140960795 + 4655060 * 2 ^ 59
def prefixEnd_4655060 : Nat := 4983230072969 + 3 ^ 40 * 4655060 * 2
def baseEnd_4655060 : Nat := 796761085172887430013925

theorem tailTrace_4655060 : CollatzResearch.WordTrace tailWord_4655060 prefixEnd_4655060 796761085172887430013925 := by
  unfold tailWord_4655060
  simp only [CollatzResearch.WordTrace]
  refine ⟨84891993257760057899129317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113189324343680077198839089 84891993257760057899129317)
  ·
    refine ⟨15917248735830010856086747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84891993257760057899129317 15917248735830010856086747)
    ·
      refine ⟨23875873103745016284130121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15917248735830010856086747 23875873103745016284130121)
      ·
        refine ⟨17906904827808762213097591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23875873103745016284130121 17906904827808762213097591)
        ·
          refine ⟨26860357241713143319646387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17906904827808762213097591 26860357241713143319646387)
          ·
            refine ⟨40290535862569714979469581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26860357241713143319646387 40290535862569714979469581)
            ·
              refine ⟨15108950948463643117301093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40290535862569714979469581 15108950948463643117301093)
              ·
                refine ⟨2832928302836933084493955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15108950948463643117301093 2832928302836933084493955)
                ·
                  refine ⟨4249392454255399626740933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2832928302836933084493955 4249392454255399626740933)
                  ·
                    refine ⟨796761085172887430013925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4249392454255399626740933 796761085172887430013925)
                    ·
                      rfl

theorem cell23_4655060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 4, 1, 4].length) (baseStart_4655060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4655060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4655060 prefixEnd_4655060 := by exact prefixLift 4655060
  have htrace : WordTrace (prefixWord ++ tailWord_4655060) baseStart_4655060 baseEnd_4655060 := by
    simpa [prefixWord, tailWord_4655060, baseEnd_4655060] using wordTrace_append hprefix tailTrace_4655060
  have hstable : (prefixWord ++ tailWord_4655060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4655060).length < 2 ^ (prefixWord ++ tailWord_4655060).sum := by decide
  have hdescent : baseEnd_4655060 < baseStart_4655060 := by decide
  rcases family_descends (prefixWord ++ tailWord_4655060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4655129 : List Nat := [1, 2, 1, 2, 1, 1, 3, 12]
def baseStart_4655129 : Nat := 118140960795 + 4655129 * 2 ^ 59
def prefixEnd_4655129 : Nat := 4983230072969 + 3 ^ 40 * 4655129 * 2
def baseEnd_4655129 : Nat := 88530321691993426669591

theorem tailTrace_4655129 : CollatzResearch.WordTrace tailWord_4655129 prefixEnd_4655129 88530321691993426669591 := by
  unfold tailWord_4655129
  simp only [CollatzResearch.WordTrace]
  refine ⟨169786503152270140582520441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113191002101513427055013627 169786503152270140582520441)
  ·
    refine ⟨127339877364202605436890331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169786503152270140582520441 127339877364202605436890331)
    ·
      refine ⟨191009816046303908155335497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127339877364202605436890331 191009816046303908155335497)
      ·
        refine ⟨143257362034727931116501623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191009816046303908155335497 143257362034727931116501623)
        ·
          refine ⟨214886043052091896674752435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143257362034727931116501623 214886043052091896674752435)
          ·
            refine ⟨322329064578137845012128653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214886043052091896674752435 322329064578137845012128653)
            ·
              refine ⟨120873399216801691879548245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 322329064578137845012128653 120873399216801691879548245)
              ·
                refine ⟨88530321691993426669591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 120873399216801691879548245 88530321691993426669591)
                ·
                  rfl

theorem cell23_4655129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 12].length) (baseStart_4655129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4655129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4655129 prefixEnd_4655129 := by exact prefixLift 4655129
  have htrace : WordTrace (prefixWord ++ tailWord_4655129) baseStart_4655129 baseEnd_4655129 := by
    simpa [prefixWord, tailWord_4655129, baseEnd_4655129] using wordTrace_append hprefix tailTrace_4655129
  have hstable : (prefixWord ++ tailWord_4655129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4655129).length < 2 ^ (prefixWord ++ tailWord_4655129).sum := by decide
  have hdescent : baseEnd_4655129 < baseStart_4655129 := by decide
  rcases family_descends (prefixWord ++ tailWord_4655129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4655133 : List Nat := [1, 4, 2, 2, 2, 1, 3, 1, 1, 6]
def baseStart_4655133 : Nat := 118140960795 + 4655133 * 2 ^ 59
def prefixEnd_4655133 : Nat := 4983230072969 + 3 ^ 40 * 4655133 * 2
def baseEnd_4655133 : Nat := 796773579868813501476313

theorem tailTrace_4655133 : CollatzResearch.WordTrace tailWord_4655133 prefixEnd_4655133 796773579868813501476313 := by
  unfold tailWord_4655133
  simp only [CollatzResearch.WordTrace]
  refine ⟨169786649044255649265666053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113191099362837099510444035 169786649044255649265666053)
  ·
    refine ⟨31834996695797934237312385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 169786649044255649265666053 31834996695797934237312385)
    ·
      refine ⟨23876247521848450677984289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31834996695797934237312385 23876247521848450677984289)
      ·
        refine ⟨17907185641386338008488217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23876247521848450677984289 17907185641386338008488217)
        ·
          refine ⟨13430389231039753506366163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17907185641386338008488217 13430389231039753506366163)
          ·
            refine ⟨20145583846559630259549245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13430389231039753506366163 20145583846559630259549245)
            ·
              refine ⟨7554593942459861347330967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20145583846559630259549245 7554593942459861347330967)
              ·
                refine ⟨11331890913689792020996451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7554593942459861347330967 11331890913689792020996451)
                ·
                  refine ⟨16997836370534688031494677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11331890913689792020996451 16997836370534688031494677)
                  ·
                    refine ⟨796773579868813501476313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16997836370534688031494677 796773579868813501476313)
                    ·
                      rfl

theorem cell23_4655133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 1, 1, 6].length) (baseStart_4655133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4655133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4655133 prefixEnd_4655133 := by exact prefixLift 4655133
  have htrace : WordTrace (prefixWord ++ tailWord_4655133) baseStart_4655133 baseEnd_4655133 := by
    simpa [prefixWord, tailWord_4655133, baseEnd_4655133] using wordTrace_append hprefix tailTrace_4655133
  have hstable : (prefixWord ++ tailWord_4655133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4655133).length < 2 ^ (prefixWord ++ tailWord_4655133).sum := by decide
  have hdescent : baseEnd_4655133 < baseStart_4655133 := by decide
  rcases family_descends (prefixWord ++ tailWord_4655133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4655183 : List Nat := [1, 1, 2, 1, 1, 2, 2, 3, 5, 3, 2]
def baseStart_4655183 : Nat := 118140960795 + 4655183 * 2 ^ 59
def prefixEnd_4655183 : Nat := 4983230072969 + 3 ^ 40 * 4655183 * 2
def baseEnd_4655183 : Nat := 2390346413639165308803709

theorem tailTrace_4655183 : CollatzResearch.WordTrace tailWord_4655183 prefixEnd_4655183 2390346413639165308803709 := by
  unfold tailWord_4655183
  simp only [CollatzResearch.WordTrace]
  refine ⟨169788472694074507804986203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113192315129383005203324135 169788472694074507804986203)
  ·
    refine ⟨254682709041111761707479305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169788472694074507804986203 254682709041111761707479305)
    ·
      refine ⟨191012031780833821280609479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 254682709041111761707479305 191012031780833821280609479)
      ·
        refine ⟨286518047671250731920914219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191012031780833821280609479 286518047671250731920914219)
        ·
          refine ⟨429777071506876097881371329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 286518047671250731920914219 429777071506876097881371329)
          ·
            refine ⟨322332803630157073411028497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 429777071506876097881371329 322332803630157073411028497)
            ·
              refine ⟨241749602722617805058271373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 322332803630157073411028497 241749602722617805058271373)
              ·
                refine ⟨90656101020981676896851765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 241749602722617805058271373 90656101020981676896851765)
                ·
                  refine ⟨8499009470717032209079853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 90656101020981676896851765 8499009470717032209079853)
                  ·
                    refine ⟨3187128551518887078404945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8499009470717032209079853 3187128551518887078404945)
                    ·
                      refine ⟨2390346413639165308803709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3187128551518887078404945 2390346413639165308803709)
                      ·
                        rfl

theorem cell23_4655183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 5, 3, 2].length) (baseStart_4655183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4655183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4655183 prefixEnd_4655183 := by exact prefixLift 4655183
  have htrace : WordTrace (prefixWord ++ tailWord_4655183) baseStart_4655183 baseEnd_4655183 := by
    simpa [prefixWord, tailWord_4655183, baseEnd_4655183] using wordTrace_append hprefix tailTrace_4655183
  have hstable : (prefixWord ++ tailWord_4655183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4655183).length < 2 ^ (prefixWord ++ tailWord_4655183).sum := by decide
  have hdescent : baseEnd_4655183 < baseStart_4655183 := by decide
  rcases family_descends (prefixWord ++ tailWord_4655183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4655200 : List Nat := [2, 1, 1, 3, 2, 4, 1, 1, 3, 3, 2]
def baseStart_4655200 : Nat := 118140960795 + 4655200 * 2 ^ 59
def prefixEnd_4655200 : Nat := 4983230072969 + 3 ^ 40 * 4655200 * 2
def baseEnd_4655200 : Nat := 2390355142810291742291131

theorem tailTrace_4655200 : CollatzResearch.WordTrace tailWord_4655200 prefixEnd_4655200 2390355142810291742291131 := by
  unfold tailWord_4655200
  simp only [CollatzResearch.WordTrace]
  refine ⟨84894546367506459854177527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113192728490008613138903369 84894546367506459854177527)
  ·
    refine ⟨127341819551259689781266291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84894546367506459854177527 127341819551259689781266291)
    ·
      refine ⟨191012729326889534671899437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127341819551259689781266291 191012729326889534671899437)
      ·
        refine ⟨71629773497583575501962289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 191012729326889534671899437 71629773497583575501962289)
        ·
          refine ⟨53722330123187681626471717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71629773497583575501962289 53722330123187681626471717)
          ·
            refine ⟨10072936898097690304963447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53722330123187681626471717 10072936898097690304963447)
            ·
              refine ⟨15109405347146535457445171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10072936898097690304963447 15109405347146535457445171)
              ·
                refine ⟨22664108020719803186167757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15109405347146535457445171 22664108020719803186167757)
                ·
                  refine ⟨8499040507769926194812909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22664108020719803186167757 8499040507769926194812909)
                  ·
                    refine ⟨3187140190413722323054841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8499040507769926194812909 3187140190413722323054841)
                    ·
                      refine ⟨2390355142810291742291131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3187140190413722323054841 2390355142810291742291131)
                      ·
                        rfl

theorem cell23_4655200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 3, 3, 2].length) (baseStart_4655200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4655200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4655200 prefixEnd_4655200 := by exact prefixLift 4655200
  have htrace : WordTrace (prefixWord ++ tailWord_4655200) baseStart_4655200 baseEnd_4655200 := by
    simpa [prefixWord, tailWord_4655200, baseEnd_4655200] using wordTrace_append hprefix tailTrace_4655200
  have hstable : (prefixWord ++ tailWord_4655200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4655200).length < 2 ^ (prefixWord ++ tailWord_4655200).sum := by decide
  have hdescent : baseEnd_4655200 < baseStart_4655200 := by decide
  rcases family_descends (prefixWord ++ tailWord_4655200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4655217 : List Nat := [1, 2, 2, 2, 1, 1, 7, 1, 1, 3, 2]
def baseStart_4655217 : Nat := 118140960795 + 4655217 * 2 ^ 59
def prefixEnd_4655217 : Nat := 4983230072969 + 3 ^ 40 * 4655217 * 2
def baseEnd_4655217 : Nat := 2390363871981418175778553

theorem tailTrace_4655217 : CollatzResearch.WordTrace tailWord_4655217 prefixEnd_4655217 2390363871981418175778553 := by
  unfold tailWord_4655217
  simp only [CollatzResearch.WordTrace]
  refine ⟨169789712775951331611723905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113193141850634221074482603 169789712775951331611723905)
  ·
    refine ⟨127342284581963498708792929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169789712775951331611723905 127342284581963498708792929)
    ·
      refine ⟨95506713436472624031594697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127342284581963498708792929 95506713436472624031594697)
      ·
        refine ⟨71630035077354468023696023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95506713436472624031594697 71630035077354468023696023)
        ·
          refine ⟨107445052616031702035544035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71630035077354468023696023 107445052616031702035544035)
          ·
            refine ⟨161167578924047553053316053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107445052616031702035544035 161167578924047553053316053)
            ·
              refine ⟨3777365131032364524687095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 161167578924047553053316053 3777365131032364524687095)
              ·
                refine ⟨5666047696548546787030643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3777365131032364524687095 5666047696548546787030643)
                ·
                  refine ⟨8499071544822820180545965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5666047696548546787030643 8499071544822820180545965)
                  ·
                    refine ⟨3187151829308557567704737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8499071544822820180545965 3187151829308557567704737)
                    ·
                      refine ⟨2390363871981418175778553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3187151829308557567704737 2390363871981418175778553)
                      ·
                        rfl

theorem cell23_4655217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 7, 1, 1, 3, 2].length) (baseStart_4655217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4655217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4655217 prefixEnd_4655217 := by exact prefixLift 4655217
  have htrace : WordTrace (prefixWord ++ tailWord_4655217) baseStart_4655217 baseEnd_4655217 := by
    simpa [prefixWord, tailWord_4655217, baseEnd_4655217] using wordTrace_append hprefix tailTrace_4655217
  have hstable : (prefixWord ++ tailWord_4655217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4655217).length < 2 ^ (prefixWord ++ tailWord_4655217).sum := by decide
  have hdescent : baseEnd_4655217 < baseStart_4655217 := by decide
  rcases family_descends (prefixWord ++ tailWord_4655217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4655226 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 5, 4, 4]
def baseStart_4655226 : Nat := 118140960795 + 4655226 * 2 ^ 59
def prefixEnd_4655226 : Nat := 4983230072969 + 3 ^ 40 * 4655226 * 2
def baseEnd_4655226 : Nat := 2390368493307308640566011

theorem tailTrace_4655226 : CollatzResearch.WordTrace tailWord_4655226 prefixEnd_4655226 2390368493307308640566011 := by
  unfold tailWord_4655226
  simp only [CollatzResearch.WordTrace]
  refine ⟨42447510258229681537200383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113193360688612484099201021 42447510258229681537200383)
  ·
    refine ⟨63671265387344522305800575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42447510258229681537200383 63671265387344522305800575)
    ·
      refine ⟨95506898081016783458700863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63671265387344522305800575 95506898081016783458700863)
      ·
        refine ⟨143260347121525175188051295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95506898081016783458700863 143260347121525175188051295)
        ·
          refine ⟨214890520682287762782076943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143260347121525175188051295 214890520682287762782076943)
          ·
            refine ⟨322335781023431644173115415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214890520682287762782076943 322335781023431644173115415)
            ·
              refine ⟨483503671535147466259673123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 322335781023431644173115415 483503671535147466259673123)
              ·
                refine ⟨725255507302721199389509685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 483503671535147466259673123 725255507302721199389509685)
                ·
                  refine ⟨67992703809630112442766533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 725255507302721199389509685 67992703809630112442766533)
                  ·
                    refine ⟨12748631964305646083018725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 67992703809630112442766533 12748631964305646083018725)
                    ·
                      refine ⟨2390368493307308640566011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12748631964305646083018725 2390368493307308640566011)
                      ·
                        rfl

theorem cell23_4655226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 5, 4, 4].length) (baseStart_4655226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4655226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4655226 prefixEnd_4655226 := by exact prefixLift 4655226
  have htrace : WordTrace (prefixWord ++ tailWord_4655226) baseStart_4655226 baseEnd_4655226 := by
    simpa [prefixWord, tailWord_4655226, baseEnd_4655226] using wordTrace_append hprefix tailTrace_4655226
  have hstable : (prefixWord ++ tailWord_4655226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4655226).length < 2 ^ (prefixWord ++ tailWord_4655226).sum := by decide
  have hdescent : baseEnd_4655226 < baseStart_4655226 := by decide
  rcases family_descends (prefixWord ++ tailWord_4655226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4655281 : List Nat := [1, 2, 2, 5, 2, 2, 1, 2, 2, 2, 2]
def baseStart_4655281 : Nat := 118140960795 + 4655281 * 2 ^ 59
def prefixEnd_4655281 : Nat := 4983230072969 + 3 ^ 40 * 4655281 * 2
def baseEnd_4655281 : Nat := 2390396734743305925378259

theorem tailTrace_4655281 : CollatzResearch.WordTrace tailWord_4655281 prefixEnd_4655281 2390396734743305925378259 := by
  unfold tailWord_4655281
  simp only [CollatzResearch.WordTrace]
  refine ⟨169792047047719470542053697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113194698031812980361369131 169792047047719470542053697)
  ·
    refine ⟨127344035285789602906540273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169792047047719470542053697 127344035285789602906540273)
    ·
      refine ⟨95508026464342202179905205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127344035285789602906540273 95508026464342202179905205)
      ·
        refine ⟨8953877481032081454366113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 95508026464342202179905205 8953877481032081454366113)
        ·
          refine ⟨6715408110774061090774585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8953877481032081454366113 6715408110774061090774585)
          ·
            refine ⟨5036556083080545818080939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6715408110774061090774585 5036556083080545818080939)
            ·
              refine ⟨7554834124620818727121409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5036556083080545818080939 7554834124620818727121409)
              ·
                refine ⟨5666125593465614045341057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7554834124620818727121409 5666125593465614045341057)
                ·
                  refine ⟨4249594195099210534005793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5666125593465614045341057 4249594195099210534005793)
                  ·
                    refine ⟨3187195646324407900504345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4249594195099210534005793 3187195646324407900504345)
                    ·
                      refine ⟨2390396734743305925378259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3187195646324407900504345 2390396734743305925378259)
                      ·
                        rfl

theorem cell23_4655281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_4655281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4655281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4655281 prefixEnd_4655281 := by exact prefixLift 4655281
  have htrace : WordTrace (prefixWord ++ tailWord_4655281) baseStart_4655281 baseEnd_4655281 := by
    simpa [prefixWord, tailWord_4655281, baseEnd_4655281] using wordTrace_append hprefix tailTrace_4655281
  have hstable : (prefixWord ++ tailWord_4655281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4655281).length < 2 ^ (prefixWord ++ tailWord_4655281).sum := by decide
  have hdescent : baseEnd_4655281 < baseStart_4655281 := by decide
  rcases family_descends (prefixWord ++ tailWord_4655281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4655340 : List Nat := [2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 3]
def baseStart_4655340 : Nat := 118140960795 + 4655340 * 2 ^ 59
def prefixEnd_4655340 : Nat := 4983230072969 + 3 ^ 40 * 4655340 * 2
def baseEnd_4655340 : Nat := 2390427030101921194540487

theorem tailTrace_4655340 : CollatzResearch.WordTrace tailWord_4655340 prefixEnd_4655340 2390427030101921194540487 := by
  unfold tailWord_4655340
  simp only [CollatzResearch.WordTrace]
  refine ⟨84897099477252861809225737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113196132636337149078967649 84897099477252861809225737)
  ·
    refine ⟨63672824607939646356919303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84897099477252861809225737 63672824607939646356919303)
    ·
      refine ⟨95509236911909469535378955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63672824607939646356919303 95509236911909469535378955)
      ·
        refine ⟨143263855367864204303068433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95509236911909469535378955 143263855367864204303068433)
        ·
          refine ⟨107447891525898153227301325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143263855367864204303068433 107447891525898153227301325)
          ·
            refine ⟨40292959322211807460237997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107447891525898153227301325 40292959322211807460237997)
            ·
              refine ⟨15109859745829427797589249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40292959322211807460237997 15109859745829427797589249)
              ·
                refine ⟨11332394809372070848191937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15109859745829427797589249 11332394809372070848191937)
                ·
                  refine ⟨8499296107029053136143953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11332394809372070848191937 8499296107029053136143953)
                  ·
                    refine ⟨6374472080271789852107965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8499296107029053136143953 6374472080271789852107965)
                    ·
                      refine ⟨2390427030101921194540487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6374472080271789852107965 2390427030101921194540487)
                      ·
                        rfl

theorem cell23_4655340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 3].length) (baseStart_4655340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4655340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4655340 prefixEnd_4655340 := by exact prefixLift 4655340
  have htrace : WordTrace (prefixWord ++ tailWord_4655340) baseStart_4655340 baseEnd_4655340 := by
    simpa [prefixWord, tailWord_4655340, baseEnd_4655340] using wordTrace_append hprefix tailTrace_4655340
  have hstable : (prefixWord ++ tailWord_4655340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4655340).length < 2 ^ (prefixWord ++ tailWord_4655340).sum := by decide
  have hdescent : baseEnd_4655340 < baseStart_4655340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4655340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4655343 : List Nat := [1, 1, 2, 1, 6, 1, 2, 1, 8]
def baseStart_4655343 : Nat := 118140960795 + 4655343 * 2 ^ 59
def prefixEnd_4655343 : Nat := 4983230072969 + 3 ^ 40 * 4655343 * 2
def baseEnd_4655343 : Nat := 265603174504876075866997

theorem tailTrace_4655343 : CollatzResearch.WordTrace tailWord_4655343 prefixEnd_4655343 265603174504876075866997 := by
  unfold tailWord_4655343
  simp only [CollatzResearch.WordTrace]
  refine ⟨169794308373494855130810683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113196205582329903420540455 169794308373494855130810683)
  ·
    refine ⟨254691462560242282696216025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169794308373494855130810683 254691462560242282696216025)
    ·
      refine ⟨191018596920181712022162019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 254691462560242282696216025 191018596920181712022162019)
      ·
        refine ⟨286527895380272568033243029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191018596920181712022162019 286527895380272568033243029)
        ·
          refine ⟨13430995095950276626558267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 286527895380272568033243029 13430995095950276626558267)
          ·
            refine ⟨20146492643925414939837401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13430995095950276626558267 20146492643925414939837401)
            ·
              refine ⟨15109869482944061204878051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20146492643925414939837401 15109869482944061204878051)
              ·
                refine ⟨22664804224416091807317077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15109869482944061204878051 22664804224416091807317077)
                ·
                  refine ⟨265603174504876075866997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22664804224416091807317077 265603174504876075866997)
                  ·
                    rfl

theorem cell23_4655343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 8].length) (baseStart_4655343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4655343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4655343 prefixEnd_4655343 := by exact prefixLift 4655343
  have htrace : WordTrace (prefixWord ++ tailWord_4655343) baseStart_4655343 baseEnd_4655343 := by
    simpa [prefixWord, tailWord_4655343, baseEnd_4655343] using wordTrace_append hprefix tailTrace_4655343
  have hstable : (prefixWord ++ tailWord_4655343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4655343).length < 2 ^ (prefixWord ++ tailWord_4655343).sum := by decide
  have hdescent : baseEnd_4655343 < baseStart_4655343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4655343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
