import V185TrunkScan23Chunk1167

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6919494 : List Nat := [6, 1, 1, 3, 1, 2, 2, 1, 6]
def baseStart_6919494 : Nat := 118140960795 + 6919494 * 2 ^ 59
def prefixEnd_6919494 : Nat := 4983230072969 + 3 ^ 40 * 6919494 * 2
def baseEnd_6919494 : Nat := 394780700877983964622537

theorem tailTrace_6919494 : CollatzResearch.WordTrace tailWord_6919494 prefixEnd_6919494 394780700877983964622537 := by
  unfold tailWord_6919494
  simp only [CollatzResearch.WordTrace]
  refine ⟨7886708737308202135498423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 168249786395908312223966357 7886708737308202135498423)
  ·
    refine ⟨11830063105962303203247635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7886708737308202135498423 11830063105962303203247635)
    ·
      refine ⟨17745094658943454804871453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11830063105962303203247635 17745094658943454804871453)
      ·
        refine ⟨6654410497103795551826795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17745094658943454804871453 6654410497103795551826795)
        ·
          refine ⟨9981615745655693327740193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6654410497103795551826795 9981615745655693327740193)
          ·
            refine ⟨7486211809241769995805145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9981615745655693327740193 7486211809241769995805145)
            ·
              refine ⟨5614658856931327496853859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7486211809241769995805145 5614658856931327496853859)
              ·
                refine ⟨8421988285396991245280789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5614658856931327496853859 8421988285396991245280789)
                ·
                  refine ⟨394780700877983964622537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8421988285396991245280789 394780700877983964622537)
                  ·
                    rfl

theorem cell23_6919494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_6919494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6919494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6919494 prefixEnd_6919494 := by exact prefixLift 6919494
  have htrace : WordTrace (prefixWord ++ tailWord_6919494) baseStart_6919494 baseEnd_6919494 := by
    simpa [prefixWord, tailWord_6919494, baseEnd_6919494] using wordTrace_append hprefix tailTrace_6919494
  have hstable : (prefixWord ++ tailWord_6919494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6919494).length < 2 ^ (prefixWord ++ tailWord_6919494).sum := by decide
  have hdescent : baseEnd_6919494 < baseStart_6919494 := by decide
  rcases family_descends (prefixWord ++ tailWord_6919494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6919496 : List Nat := [2, 1, 3, 1, 1, 2, 1, 4, 3, 2, 3]
def baseStart_6919496 : Nat := 118140960795 + 6919496 * 2 ^ 59
def prefixEnd_6919496 : Nat := 4983230072969 + 3 ^ 40 * 6919496 * 2
def baseEnd_6919496 : Nat := 3553027334863164673777823

theorem tailTrace_6919496 : CollatzResearch.WordTrace tailWord_6919496 prefixEnd_6919496 3553027334863164673777823 := by
  unfold tailWord_6919496
  simp only [CollatzResearch.WordTrace]
  refine ⟨126187376269927611338761171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168249835026570148451681561 126187376269927611338761171)
  ·
    refine ⟨189281064404891417008141757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126187376269927611338761171 189281064404891417008141757)
    ·
      refine ⟨70980399151834281378053159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189281064404891417008141757 70980399151834281378053159)
      ·
        refine ⟨106470598727751422067079739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70980399151834281378053159 106470598727751422067079739)
        ·
          refine ⟨159705898091627133100619609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106470598727751422067079739 159705898091627133100619609)
          ·
            refine ⟨119779423568720349825464707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159705898091627133100619609 119779423568720349825464707)
            ·
              refine ⟨179669135353080524738197061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119779423568720349825464707 179669135353080524738197061)
              ·
                refine ⟨33687962878702598388411949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 179669135353080524738197061 33687962878702598388411949)
                ·
                  refine ⟨12632986079513474395654481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33687962878702598388411949 12632986079513474395654481)
                  ·
                    refine ⟨9474739559635105796740861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12632986079513474395654481 9474739559635105796740861)
                    ·
                      refine ⟨3553027334863164673777823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9474739559635105796740861 3553027334863164673777823)
                      ·
                        rfl

theorem cell23_6919496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 3, 2, 3].length) (baseStart_6919496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6919496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6919496 prefixEnd_6919496 := by exact prefixLift 6919496
  have htrace : WordTrace (prefixWord ++ tailWord_6919496) baseStart_6919496 baseEnd_6919496 := by
    simpa [prefixWord, tailWord_6919496, baseEnd_6919496] using wordTrace_append hprefix tailTrace_6919496
  have hstable : (prefixWord ++ tailWord_6919496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6919496).length < 2 ^ (prefixWord ++ tailWord_6919496).sum := by decide
  have hdescent : baseEnd_6919496 < baseStart_6919496 := by decide
  rcases family_descends (prefixWord ++ tailWord_6919496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6919506 : List Nat := [3, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4]
def baseStart_6919506 : Nat := 118140960795 + 6919506 * 2 ^ 59
def prefixEnd_6919506 : Nat := 4983230072969 + 3 ^ 40 * 6919506 * 2
def baseEnd_6919506 : Nat := 3553032469669709634652777

theorem tailTrace_6919506 : CollatzResearch.WordTrace tailWord_6919506 prefixEnd_6919506 3553032469669709634652777 := by
  unfold tailWord_6919506
  simp only [CollatzResearch.WordTrace]
  refine ⟨63093779317454748596346593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168250078179879329590257581 63093779317454748596346593)
  ·
    refine ⟨47320334488091061447259945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63093779317454748596346593 47320334488091061447259945)
    ·
      refine ⟨35490250866068296085444959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47320334488091061447259945 35490250866068296085444959)
      ·
        refine ⟨53235376299102444128167439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35490250866068296085444959 53235376299102444128167439)
        ·
          refine ⟨79853064448653666192251159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53235376299102444128167439 79853064448653666192251159)
          ·
            refine ⟨119779596672980499288376739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79853064448653666192251159 119779596672980499288376739)
            ·
              refine ⟨179669395009470748932565109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119779596672980499288376739 179669395009470748932565109)
              ·
                refine ⟨16844005782137882712427979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 179669395009470748932565109 16844005782137882712427979)
                ·
                  refine ⟨25266008673206824068641969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16844005782137882712427979 25266008673206824068641969)
                  ·
                    refine ⟨18949506504905118051481477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25266008673206824068641969 18949506504905118051481477)
                    ·
                      refine ⟨3553032469669709634652777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18949506504905118051481477 3553032469669709634652777)
                      ·
                        rfl

theorem cell23_6919506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_6919506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6919506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6919506 prefixEnd_6919506 := by exact prefixLift 6919506
  have htrace : WordTrace (prefixWord ++ tailWord_6919506) baseStart_6919506 baseEnd_6919506 := by
    simpa [prefixWord, tailWord_6919506, baseEnd_6919506] using wordTrace_append hprefix tailTrace_6919506
  have hstable : (prefixWord ++ tailWord_6919506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6919506).length < 2 ^ (prefixWord ++ tailWord_6919506).sum := by decide
  have hdescent : baseEnd_6919506 < baseStart_6919506 := by decide
  rcases family_descends (prefixWord ++ tailWord_6919506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6919513 : List Nat := [1, 2, 1, 2, 2, 2, 5, 2, 1, 2, 3]
def baseStart_6919513 : Nat := 118140960795 + 6919513 * 2 ^ 59
def prefixEnd_6919513 : Nat := 4983230072969 + 3 ^ 40 * 6919513 * 2
def baseEnd_6919513 : Nat := 3553036064034291107265245

theorem tailTrace_6919513 : CollatzResearch.WordTrace tailWord_6919513 prefixEnd_6919513 3553036064034291107265245 := by
  unfold tailWord_6919513
  simp only [CollatzResearch.WordTrace]
  refine ⟨252375372580793634580891193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168250248387195756387260795 252375372580793634580891193)
  ·
    refine ⟨189281529435595225935668395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252375372580793634580891193 189281529435595225935668395)
    ·
      refine ⟨283922294153392838903502593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189281529435595225935668395 283922294153392838903502593)
      ·
        refine ⟨212941720615044629177626945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283922294153392838903502593 212941720615044629177626945)
        ·
          refine ⟨159706290461283471883220209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212941720615044629177626945 159706290461283471883220209)
          ·
            refine ⟨119779717845962603912415157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159706290461283471883220209 119779717845962603912415157)
            ·
              refine ⟨11229348548058994116788921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 119779717845962603912415157 11229348548058994116788921)
              ·
                refine ⟨8422011411044245587591691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11229348548058994116788921 8422011411044245587591691)
                ·
                  refine ⟨12633017116566368381387537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8422011411044245587591691 12633017116566368381387537)
                  ·
                    refine ⟨9474762837424776286040653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12633017116566368381387537 9474762837424776286040653)
                    ·
                      refine ⟨3553036064034291107265245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9474762837424776286040653 3553036064034291107265245)
                      ·
                        rfl

theorem cell23_6919513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 2, 1, 2, 3].length) (baseStart_6919513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6919513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6919513 prefixEnd_6919513 := by exact prefixLift 6919513
  have htrace : WordTrace (prefixWord ++ tailWord_6919513) baseStart_6919513 baseEnd_6919513 := by
    simpa [prefixWord, tailWord_6919513, baseEnd_6919513] using wordTrace_append hprefix tailTrace_6919513
  have hstable : (prefixWord ++ tailWord_6919513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6919513).length < 2 ^ (prefixWord ++ tailWord_6919513).sum := by decide
  have hdescent : baseEnd_6919513 < baseStart_6919513 := by decide
  rcases family_descends (prefixWord ++ tailWord_6919513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6919530 : List Nat := [3, 1, 3, 3, 2, 2, 1, 1, 1, 1, 5]
def baseStart_6919530 : Nat := 118140960795 + 6919530 * 2 ^ 59
def prefixEnd_6919530 : Nat := 4983230072969 + 3 ^ 40 * 6919530 * 2
def baseEnd_6919530 : Nat := 3553044793205417540752667

theorem tailTrace_6919530 : CollatzResearch.WordTrace tailWord_6919530 prefixEnd_6919530 3553044793205417540752667 := by
  unfold tailWord_6919530
  simp only [CollatzResearch.WordTrace]
  refine ⟨63093998155433011621065011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168250661747821364322840029 63093998155433011621065011)
  ·
    refine ⟨94640997233149517431597517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63093998155433011621065011 94640997233149517431597517)
    ·
      refine ⟨35490373962431069036849069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94640997233149517431597517 35490373962431069036849069)
      ·
        refine ⟨13308890235911650888818401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35490373962431069036849069 13308890235911650888818401)
        ·
          refine ⟨9981667676933738166613801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13308890235911650888818401 9981667676933738166613801)
          ·
            refine ⟨7486250757700303624960351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9981667676933738166613801 7486250757700303624960351)
            ·
              refine ⟨11229376136550455437440527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7486250757700303624960351 11229376136550455437440527)
              ·
                refine ⟨16844064204825683156160791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11229376136550455437440527 16844064204825683156160791)
                ·
                  refine ⟨25266096307238524734241187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16844064204825683156160791 25266096307238524734241187)
                  ·
                    refine ⟨37899144460857787101361781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25266096307238524734241187 37899144460857787101361781)
                    ·
                      refine ⟨3553044793205417540752667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37899144460857787101361781 3553044793205417540752667)
                      ·
                        rfl

theorem cell23_6919530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_6919530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6919530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6919530 prefixEnd_6919530 := by exact prefixLift 6919530
  have htrace : WordTrace (prefixWord ++ tailWord_6919530) baseStart_6919530 baseEnd_6919530 := by
    simpa [prefixWord, tailWord_6919530, baseEnd_6919530] using wordTrace_append hprefix tailTrace_6919530
  have hstable : (prefixWord ++ tailWord_6919530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6919530).length < 2 ^ (prefixWord ++ tailWord_6919530).sum := by decide
  have hdescent : baseEnd_6919530 < baseStart_6919530 := by decide
  rcases family_descends (prefixWord ++ tailWord_6919530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6919560 : List Nat := [2, 1, 3, 3, 1, 2, 2, 3, 2, 1, 3]
def baseStart_6919560 : Nat := 118140960795 + 6919560 * 2 ^ 59
def prefixEnd_6919560 : Nat := 4983230072969 + 3 ^ 40 * 6919560 * 2
def baseEnd_6919560 : Nat := 3553060197625052423377529

theorem tailTrace_6919560 : CollatzResearch.WordTrace tailWord_6919560 prefixEnd_6919560 3553060197625052423377529 := by
  unfold tailWord_6919560
  simp only [CollatzResearch.WordTrace]
  refine ⟨126188543405811680803926067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168251391207748907738568089 126188543405811680803926067)
  ·
    refine ⟨189282815108717521205889101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126188543405811680803926067 189282815108717521205889101)
    ·
      refine ⟨70981055665769070452208413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189282815108717521205889101 70981055665769070452208413)
      ·
        refine ⟨26617895874663401419578155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70981055665769070452208413 26617895874663401419578155)
        ·
          refine ⟨39926843811995102129367233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26617895874663401419578155 39926843811995102129367233)
          ·
            refine ⟨29945132858996326597025425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39926843811995102129367233 29945132858996326597025425)
            ·
              refine ⟨22458849644247244947769069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29945132858996326597025425 22458849644247244947769069)
              ·
                refine ⟨8422068616592716855413401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22458849644247244947769069 8422068616592716855413401)
                ·
                  refine ⟨6316551462444537641560051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8422068616592716855413401 6316551462444537641560051)
                  ·
                    refine ⟨9474827193666806462340077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6316551462444537641560051 9474827193666806462340077)
                    ·
                      refine ⟨3553060197625052423377529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9474827193666806462340077 3553060197625052423377529)
                      ·
                        rfl

theorem cell23_6919560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_6919560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6919560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6919560 prefixEnd_6919560 := by exact prefixLift 6919560
  have htrace : WordTrace (prefixWord ++ tailWord_6919560) baseStart_6919560 baseEnd_6919560 := by
    simpa [prefixWord, tailWord_6919560, baseEnd_6919560] using wordTrace_append hprefix tailTrace_6919560
  have hstable : (prefixWord ++ tailWord_6919560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6919560).length < 2 ^ (prefixWord ++ tailWord_6919560).sum := by decide
  have hdescent : baseEnd_6919560 < baseStart_6919560 := by decide
  rcases family_descends (prefixWord ++ tailWord_6919560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6919579 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 6]
def baseStart_6919579 : Nat := 118140960795 + 6919579 * 2 ^ 59
def prefixEnd_6919579 : Nat := 4983230072969 + 3 ^ 40 * 6919579 * 2
def baseEnd_6919579 : Nat := 3553069953757487849039941

theorem tailTrace_6919579 : CollatzResearch.WordTrace tailWord_6919579 prefixEnd_6919579 3553069953757487849039941 := by
  unfold tailWord_6919579
  simp only [CollatzResearch.WordTrace]
  refine ⟨252377779798554527852793791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168251853199036351901862527 252377779798554527852793791)
  ·
    refine ⟨378566669697831791779190687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252377779798554527852793791 378566669697831791779190687)
    ·
      refine ⟨567850004546747687668786031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378566669697831791779190687 567850004546747687668786031)
      ·
        refine ⟨851775006820121531503179047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 567850004546747687668786031 851775006820121531503179047)
        ·
          refine ⟨1277662510230182297254768571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 851775006820121531503179047 1277662510230182297254768571)
          ·
            refine ⟨1916493765345273445882152857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1277662510230182297254768571 1916493765345273445882152857)
            ·
              refine ⟨1437370324008955084411614643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1916493765345273445882152857 1437370324008955084411614643)
              ·
                refine ⟨2156055486013432626617421965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1437370324008955084411614643 2156055486013432626617421965)
                ·
                  refine ⟨808520807255037234981533237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2156055486013432626617421965 808520807255037234981533237)
                  ·
                    refine ⟨75798825680159740779518741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 808520807255037234981533237 75798825680159740779518741)
                    ·
                      refine ⟨3553069953757487849039941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75798825680159740779518741 3553069953757487849039941)
                      ·
                        rfl

theorem cell23_6919579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 6].length) (baseStart_6919579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6919579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6919579 prefixEnd_6919579 := by exact prefixLift 6919579
  have htrace : WordTrace (prefixWord ++ tailWord_6919579) baseStart_6919579 baseEnd_6919579 := by
    simpa [prefixWord, tailWord_6919579, baseEnd_6919579] using wordTrace_append hprefix tailTrace_6919579
  have hstable : (prefixWord ++ tailWord_6919579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6919579).length < 2 ^ (prefixWord ++ tailWord_6919579).sum := by decide
  have hdescent : baseEnd_6919579 < baseStart_6919579 := by decide
  rcases family_descends (prefixWord ++ tailWord_6919579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6919596 : List Nat := [2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 4]
def baseStart_6919596 : Nat := 118140960795 + 6919596 * 2 ^ 59
def prefixEnd_6919596 : Nat := 4983230072969 + 3 ^ 40 * 6919596 * 2
def baseEnd_6919596 : Nat := 3553078682928614282527363

theorem tailTrace_6919596 : CollatzResearch.WordTrace tailWord_6919596 prefixEnd_6919596 3553078682928614282527363 := by
  unfold tailWord_6919596
  simp only [CollatzResearch.WordTrace]
  refine ⟨126189199919746469878081321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168252266559661959837441761 126189199919746469878081321)
  ·
    refine ⟨94641899939809852408560991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126189199919746469878081321 94641899939809852408560991)
    ·
      refine ⟨141962849909714778612841487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94641899939809852408560991 141962849909714778612841487)
      ·
        refine ⟨212944274864572167919262231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141962849909714778612841487 212944274864572167919262231)
        ·
          refine ⟨319416412296858251878893347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212944274864572167919262231 319416412296858251878893347)
          ·
            refine ⟨479124618445287377818340021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319416412296858251878893347 479124618445287377818340021)
            ·
              refine ⟨44917932979245691670469377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 479124618445287377818340021 44917932979245691670469377)
              ·
                refine ⟨33688449734434268752852033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44917932979245691670469377 33688449734434268752852033)
                ·
                  refine ⟨25266337300825701564639025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33688449734434268752852033 25266337300825701564639025)
                  ·
                    refine ⟨18949752975619276173479269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25266337300825701564639025 18949752975619276173479269)
                    ·
                      refine ⟨3553078682928614282527363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18949752975619276173479269 3553078682928614282527363)
                      ·
                        rfl

theorem cell23_6919596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 4].length) (baseStart_6919596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6919596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6919596 prefixEnd_6919596 := by exact prefixLift 6919596
  have htrace : WordTrace (prefixWord ++ tailWord_6919596) baseStart_6919596 baseEnd_6919596 := by
    simpa [prefixWord, tailWord_6919596, baseEnd_6919596] using wordTrace_append hprefix tailTrace_6919596
  have hstable : (prefixWord ++ tailWord_6919596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6919596).length < 2 ^ (prefixWord ++ tailWord_6919596).sum := by decide
  have hdescent : baseEnd_6919596 < baseStart_6919596 := by decide
  rcases family_descends (prefixWord ++ tailWord_6919596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6919600 : List Nat := [2, 1, 1, 1, 2, 1, 1, 8, 2, 2, 2]
def baseStart_6919600 : Nat := 118140960795 + 6919600 * 2 ^ 59
def prefixEnd_6919600 : Nat := 4983230072969 + 3 ^ 40 * 6919600 * 2
def baseEnd_6919600 : Nat := 3553080736851232266877345

theorem tailTrace_6919600 : CollatzResearch.WordTrace tailWord_6919600 prefixEnd_6919600 3553080736851232266877345 := by
  unfold tailWord_6919600
  simp only [CollatzResearch.WordTrace]
  refine ⟨126189272865739224219654127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168252363820985632292872169 126189272865739224219654127)
  ·
    refine ⟨189283909298608836329481191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126189272865739224219654127 189283909298608836329481191)
    ·
      refine ⟨283925863947913254494221787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189283909298608836329481191 283925863947913254494221787)
      ·
        refine ⟨425888795921869881741332681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283925863947913254494221787 425888795921869881741332681)
        ·
          refine ⟨319416596941402411305999511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 425888795921869881741332681 319416596941402411305999511)
          ·
            refine ⟨479124895412103616958999267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319416596941402411305999511 479124895412103616958999267)
            ·
              refine ⟨718687343118155425438498901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 479124895412103616958999267 718687343118155425438498901)
              ·
                refine ⟨8422117302165883891857409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 718687343118155425438498901 8422117302165883891857409)
                ·
                  refine ⟨6316587976624412918893057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8422117302165883891857409 6316587976624412918893057)
                  ·
                    refine ⟨4737440982468309689169793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6316587976624412918893057 4737440982468309689169793)
                    ·
                      refine ⟨3553080736851232266877345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4737440982468309689169793 3553080736851232266877345)
                      ·
                        rfl

theorem cell23_6919600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 8, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 8, 2, 2, 2].length) (baseStart_6919600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6919600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6919600 prefixEnd_6919600 := by exact prefixLift 6919600
  have htrace : WordTrace (prefixWord ++ tailWord_6919600) baseStart_6919600 baseEnd_6919600 := by
    simpa [prefixWord, tailWord_6919600, baseEnd_6919600] using wordTrace_append hprefix tailTrace_6919600
  have hstable : (prefixWord ++ tailWord_6919600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6919600).length < 2 ^ (prefixWord ++ tailWord_6919600).sum := by decide
  have hdescent : baseEnd_6919600 < baseStart_6919600 := by decide
  rcases family_descends (prefixWord ++ tailWord_6919600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6919653 : List Nat := [1, 3, 1, 5, 1, 1, 1, 1, 4, 5]
def baseStart_6919653 : Nat := 118140960795 + 6919653 * 2 ^ 59
def prefixEnd_6919653 : Nat := 4983230072969 + 3 ^ 40 * 6919653 * 2
def baseEnd_6919653 : Nat := 1184369317108640186504867

theorem tailTrace_6919653 : CollatzResearch.WordTrace tailWord_6919653 prefixEnd_6919653 1184369317108640186504867 := by
  unfold tailWord_6919653
  simp only [CollatzResearch.WordTrace]
  refine ⟨252380478800286438490987613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168253652533524292327325075 252380478800286438490987613)
  ·
    refine ⟨94642679550107414434120355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252380478800286438490987613 94642679550107414434120355)
    ·
      refine ⟨141964019325161121651180533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94642679550107414434120355 141964019325161121651180533)
      ·
        refine ⟨13309126811733855154798175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 141964019325161121651180533 13309126811733855154798175)
        ·
          refine ⟨19963690217600782732197263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13309126811733855154798175 19963690217600782732197263)
          ·
            refine ⟨29945535326401174098295895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19963690217600782732197263 29945535326401174098295895)
            ·
              refine ⟨44918302989601761147443843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29945535326401174098295895 44918302989601761147443843)
              ·
                refine ⟨67377454484402641721165765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44918302989601761147443843 67377454484402641721165765)
                ·
                  refine ⟨12633272715825495322718581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67377454484402641721165765 12633272715825495322718581)
                  ·
                    refine ⟨1184369317108640186504867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12633272715825495322718581 1184369317108640186504867)
                    ·
                      rfl

theorem cell23_6919653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 4, 5].length) (baseStart_6919653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6919653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6919653 prefixEnd_6919653 := by exact prefixLift 6919653
  have htrace : WordTrace (prefixWord ++ tailWord_6919653) baseStart_6919653 baseEnd_6919653 := by
    simpa [prefixWord, tailWord_6919653, baseEnd_6919653] using wordTrace_append hprefix tailTrace_6919653
  have hstable : (prefixWord ++ tailWord_6919653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6919653).length < 2 ^ (prefixWord ++ tailWord_6919653).sum := by decide
  have hdescent : baseEnd_6919653 < baseStart_6919653 := by decide
  rcases family_descends (prefixWord ++ tailWord_6919653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6919673 : List Nat := [1, 2, 1, 3, 1, 2, 1, 3, 1, 6, 2]
def baseStart_6919673 : Nat := 118140960795 + 6919673 * 2 ^ 59
def prefixEnd_6919673 : Nat := 4983230072969 + 3 ^ 40 * 6919673 * 2
def baseEnd_6919673 : Nat := 3553118220939010481264509

theorem tailTrace_6919673 : CollatzResearch.WordTrace tailWord_6919673 prefixEnd_6919673 3553118220939010481264509 := by
  unfold tailWord_6919673
  simp only [CollatzResearch.WordTrace]
  refine ⟨252381208260213981906715673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168254138840142654604477115 252381208260213981906715673)
  ·
    refine ⟨189285906195160486430036755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252381208260213981906715673 189285906195160486430036755)
    ·
      refine ⟨283928859292740729645055133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189285906195160486430036755 283928859292740729645055133)
      ·
        refine ⟨106473322234777773616895675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 283928859292740729645055133 106473322234777773616895675)
        ·
          refine ⟨159709983352166660425343513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106473322234777773616895675 159709983352166660425343513)
          ·
            refine ⟨119782487514124995319007635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159709983352166660425343513 119782487514124995319007635)
            ·
              refine ⟨179673731271187492978511453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119782487514124995319007635 179673731271187492978511453)
              ·
                refine ⟨67377649226695309866941795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 179673731271187492978511453 67377649226695309866941795)
                ·
                  refine ⟨101066473840042964800412693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67377649226695309866941795 101066473840042964800412693)
                  ·
                    refine ⟨4737490961252013975019345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 101066473840042964800412693 4737490961252013975019345)
                    ·
                      refine ⟨3553118220939010481264509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4737490961252013975019345 3553118220939010481264509)
                      ·
                        rfl

theorem cell23_6919673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 6, 2].length) (baseStart_6919673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6919673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6919673 prefixEnd_6919673 := by exact prefixLift 6919673
  have htrace : WordTrace (prefixWord ++ tailWord_6919673) baseStart_6919673 baseEnd_6919673 := by
    simpa [prefixWord, tailWord_6919673, baseEnd_6919673] using wordTrace_append hprefix tailTrace_6919673
  have hstable : (prefixWord ++ tailWord_6919673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6919673).length < 2 ^ (prefixWord ++ tailWord_6919673).sum := by decide
  have hdescent : baseEnd_6919673 < baseStart_6919673 := by decide
  rcases family_descends (prefixWord ++ tailWord_6919673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6919690 : List Nat := [3, 1, 2, 2, 2, 3, 2, 1, 2, 1, 4]
def baseStart_6919690 : Nat := 118140960795 + 6919690 * 2 ^ 59
def prefixEnd_6919690 : Nat := 4983230072969 + 3 ^ 40 * 6919690 * 2
def baseEnd_6919690 : Nat := 3553126950110136914751931

theorem tailTrace_6919690 : CollatzResearch.WordTrace tailWord_6919690 prefixEnd_6919690 3553126950110136914751931 := by
  unfold tailWord_6919690
  simp only [CollatzResearch.WordTrace]
  refine ⟨63095457075288098452521131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168254552200768262540056349 63095457075288098452521131)
  ·
    refine ⟨94643185612932147678781697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63095457075288098452521131 94643185612932147678781697)
    ·
      refine ⟨70982389209699110759086273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94643185612932147678781697 70982389209699110759086273)
      ·
        refine ⟨53236791907274333069314705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70982389209699110759086273 53236791907274333069314705)
        ·
          refine ⟨39927593930455749801986029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53236791907274333069314705 39927593930455749801986029)
          ·
            refine ⟨14972847723920906175744761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39927593930455749801986029 14972847723920906175744761)
            ·
              refine ⟨11229635792940679631808571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14972847723920906175744761 11229635792940679631808571)
              ·
                refine ⟨16844453689411019447712857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11229635792940679631808571 16844453689411019447712857)
                ·
                  refine ⟨12633340267058264585784643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16844453689411019447712857 12633340267058264585784643)
                  ·
                    refine ⟨18950010400587396878676965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12633340267058264585784643 18950010400587396878676965)
                    ·
                      refine ⟨3553126950110136914751931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18950010400587396878676965 3553126950110136914751931)
                      ·
                        rfl

theorem cell23_6919690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 1, 2, 1, 4].length) (baseStart_6919690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6919690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6919690 prefixEnd_6919690 := by exact prefixLift 6919690
  have htrace : WordTrace (prefixWord ++ tailWord_6919690) baseStart_6919690 baseEnd_6919690 := by
    simpa [prefixWord, tailWord_6919690, baseEnd_6919690] using wordTrace_append hprefix tailTrace_6919690
  have hstable : (prefixWord ++ tailWord_6919690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6919690).length < 2 ^ (prefixWord ++ tailWord_6919690).sum := by decide
  have hdescent : baseEnd_6919690 < baseStart_6919690 := by decide
  rcases family_descends (prefixWord ++ tailWord_6919690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6919713 : List Nat := [1, 2, 3, 2, 2, 2, 1, 4, 6]
def baseStart_6919713 : Nat := 118140960795 + 6919713 * 2 ^ 59
def prefixEnd_6919713 : Nat := 4983230072969 + 3 ^ 40 * 6919713 * 2
def baseEnd_6919713 : Nat := 394793195573910036084925

theorem tailTrace_6919713 : CollatzResearch.WordTrace tailWord_6919713 prefixEnd_6919713 394793195573910036084925 := by
  unfold tailWord_6919713
  simp only [CollatzResearch.WordTrace]
  refine ⟨252382667180069068738171793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168255111453379379158781195 252382667180069068738171793)
  ·
    refine ⟨189287000385051801553628845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252382667180069068738171793 189287000385051801553628845)
    ·
      refine ⟨70982625144394425582610817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189287000385051801553628845 70982625144394425582610817)
      ·
        refine ⟨53236968858295819186958113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70982625144394425582610817 53236968858295819186958113)
        ·
          refine ⟨39927726643721864390218585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53236968858295819186958113 39927726643721864390218585)
          ·
            refine ⟨29945794982791398292663939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39927726643721864390218585 29945794982791398292663939)
            ·
              refine ⟨44918692474187097438995909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29945794982791398292663939 44918692474187097438995909)
              ·
                refine ⟨8422254838910080769811733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44918692474187097438995909 8422254838910080769811733)
                ·
                  refine ⟨394793195573910036084925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8422254838910080769811733 394793195573910036084925)
                  ·
                    rfl

theorem cell23_6919713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 4, 6].length) (baseStart_6919713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6919713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6919713 prefixEnd_6919713 := by exact prefixLift 6919713
  have htrace : WordTrace (prefixWord ++ tailWord_6919713) baseStart_6919713 baseEnd_6919713 := by
    simpa [prefixWord, tailWord_6919713, baseEnd_6919713] using wordTrace_append hprefix tailTrace_6919713
  have hstable : (prefixWord ++ tailWord_6919713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6919713).length < 2 ^ (prefixWord ++ tailWord_6919713).sum := by decide
  have hdescent : baseEnd_6919713 < baseStart_6919713 := by decide
  rcases family_descends (prefixWord ++ tailWord_6919713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6919743 : List Nat := [1, 1, 2, 2, 3, 3, 2, 1, 3, 5]
def baseStart_6919743 : Nat := 118140960795 + 6919743 * 2 ^ 59
def prefixEnd_6919743 : Nat := 4983230072969 + 3 ^ 40 * 6919743 * 2
def baseEnd_6919743 : Nat := 1184384721528275069129729

theorem tailTrace_6919743 : CollatzResearch.WordTrace tailWord_6919743 prefixEnd_6919743 1184384721528275069129729 := by
  unfold tailWord_6919743
  simp only [CollatzResearch.WordTrace]
  refine ⟨252383761369960383861763883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168255840913306922574509255 252383761369960383861763883)
  ·
    refine ⟨378575642054940575792645825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252383761369960383861763883 378575642054940575792645825)
    ·
      refine ⟨283931731541205431844484369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 378575642054940575792645825 283931731541205431844484369)
      ·
        refine ⟨212948798655904073883363277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283931731541205431844484369 212948798655904073883363277)
        ·
          refine ⟨79855799495964027706261229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212948798655904073883363277 79855799495964027706261229)
          ·
            refine ⟨29945924810986510389847961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79855799495964027706261229 29945924810986510389847961)
            ·
              refine ⟨22459443608239882792385971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29945924810986510389847961 22459443608239882792385971)
              ·
                refine ⟨33689165412359824188578957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22459443608239882792385971 33689165412359824188578957)
                ·
                  refine ⟨12633437029634934070717109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33689165412359824188578957 12633437029634934070717109)
                  ·
                    refine ⟨1184384721528275069129729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12633437029634934070717109 1184384721528275069129729)
                    ·
                      rfl

theorem cell23_6919743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 3, 5].length) (baseStart_6919743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6919743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6919743 prefixEnd_6919743 := by exact prefixLift 6919743
  have htrace : WordTrace (prefixWord ++ tailWord_6919743) baseStart_6919743 baseEnd_6919743 := by
    simpa [prefixWord, tailWord_6919743, baseEnd_6919743] using wordTrace_append hprefix tailTrace_6919743
  have hstable : (prefixWord ++ tailWord_6919743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6919743).length < 2 ^ (prefixWord ++ tailWord_6919743).sum := by decide
  have hdescent : baseEnd_6919743 < baseStart_6919743 := by decide
  rcases family_descends (prefixWord ++ tailWord_6919743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6919783 : List Nat := [1, 1, 5, 1, 1, 1, 3, 1, 3, 1, 5]
def baseStart_6919783 : Nat := 118140960795 + 6919783 * 2 ^ 59
def prefixEnd_6919783 : Nat := 4983230072969 + 3 ^ 40 * 6919783 * 2
def baseEnd_6919783 : Nat := 3553174703811005050889003

theorem tailTrace_6919783 : CollatzResearch.WordTrace tailWord_6919783 prefixEnd_6919783 3553174703811005050889003 := by
  unfold tailWord_6919783
  simp only [CollatzResearch.WordTrace]
  refine ⟨252385220289815470693220003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168256813526543647128813335 252385220289815470693220003)
  ·
    refine ⟨378577830434723206039830005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252385220289815470693220003 378577830434723206039830005)
    ·
      refine ⟨35491671603255300566234063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 378577830434723206039830005 35491671603255300566234063)
      ·
        refine ⟨53237507404882950849351095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35491671603255300566234063 53237507404882950849351095)
        ·
          refine ⟨79856261107324426274026643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53237507404882950849351095 79856261107324426274026643)
          ·
            refine ⟨119784391660986639411039965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79856261107324426274026643 119784391660986639411039965)
            ·
              refine ⟨44919146872869989779139987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119784391660986639411039965 44919146872869989779139987)
              ·
                refine ⟨67378720309304984668709981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44919146872869989779139987 67378720309304984668709981)
                ·
                  refine ⟨25267020115989369250766243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67378720309304984668709981 25267020115989369250766243)
                  ·
                    refine ⟨37900530173984053876149365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25267020115989369250766243 37900530173984053876149365)
                    ·
                      refine ⟨3553174703811005050889003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37900530173984053876149365 3553174703811005050889003)
                      ·
                        rfl

theorem cell23_6919783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_6919783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6919783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6919783 prefixEnd_6919783 := by exact prefixLift 6919783
  have htrace : WordTrace (prefixWord ++ tailWord_6919783) baseStart_6919783 baseEnd_6919783 := by
    simpa [prefixWord, tailWord_6919783, baseEnd_6919783] using wordTrace_append hprefix tailTrace_6919783
  have hstable : (prefixWord ++ tailWord_6919783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6919783).length < 2 ^ (prefixWord ++ tailWord_6919783).sum := by decide
  have hdescent : baseEnd_6919783 < baseStart_6919783 := by decide
  rcases family_descends (prefixWord ++ tailWord_6919783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6919797 : List Nat := [1, 3, 4, 2, 1, 1, 1, 4, 1, 1, 4]
def baseStart_6919797 : Nat := 118140960795 + 6919797 * 2 ^ 59
def prefixEnd_6919797 : Nat := 4983230072969 + 3 ^ 40 * 6919797 * 2
def baseEnd_6919797 : Nat := 3553181892540167996113939

theorem tailTrace_6919797 : CollatzResearch.WordTrace tailWord_6919797 prefixEnd_6919797 3553181892540167996113939 := by
  unfold tailWord_6919797
  simp only [CollatzResearch.WordTrace]
  refine ⟨252385730911764751084229645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168257153941176500722819763 252385730911764751084229645)
  ·
    refine ⟨94644649091911781656586117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252385730911764751084229645 94644649091911781656586117)
    ·
      refine ⟨17745871704733459060609897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94644649091911781656586117 17745871704733459060609897)
      ·
        refine ⟨13309403778550094295457423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17745871704733459060609897 13309403778550094295457423)
        ·
          refine ⟨19964105667825141443186135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13309403778550094295457423 19964105667825141443186135)
          ·
            refine ⟨29946158501737712164779203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19964105667825141443186135 29946158501737712164779203)
            ·
              refine ⟨44919237752606568247168805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29946158501737712164779203 44919237752606568247168805)
              ·
                refine ⟨8422357078613731546344151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44919237752606568247168805 8422357078613731546344151)
                ·
                  refine ⟨12633535617920597319516227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8422357078613731546344151 12633535617920597319516227)
                  ·
                    refine ⟨18950303426880895979274341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12633535617920597319516227 18950303426880895979274341)
                    ·
                      refine ⟨3553181892540167996113939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18950303426880895979274341 3553181892540167996113939)
                      ·
                        rfl

theorem cell23_6919797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_6919797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6919797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6919797 prefixEnd_6919797 := by exact prefixLift 6919797
  have htrace : WordTrace (prefixWord ++ tailWord_6919797) baseStart_6919797 baseEnd_6919797 := by
    simpa [prefixWord, tailWord_6919797, baseEnd_6919797] using wordTrace_append hprefix tailTrace_6919797
  have hstable : (prefixWord ++ tailWord_6919797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6919797).length < 2 ^ (prefixWord ++ tailWord_6919797).sum := by decide
  have hdescent : baseEnd_6919797 < baseStart_6919797 := by decide
  rcases family_descends (prefixWord ++ tailWord_6919797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6919848 : List Nat := [2, 1, 7, 1, 1, 2, 1, 2, 1, 1, 4]
def baseStart_6919848 : Nat := 118140960795 + 6919848 * 2 ^ 59
def prefixEnd_6919848 : Nat := 4983230072969 + 3 ^ 40 * 6919848 * 2
def baseEnd_6919848 : Nat := 3553208080053547296576205

theorem tailTrace_6919848 : CollatzResearch.WordTrace tailWord_6919848 prefixEnd_6919848 3553208080053547296576205 := by
  unfold tailWord_6919848
  simp only [CollatzResearch.WordTrace]
  refine ⟨126193795517289993397168099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168258394023053324529557465 126193795517289993397168099)
  ·
    refine ⟨189290693275934990095752149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126193795517289993397168099 189290693275934990095752149)
    ·
      refine ⟨4436500623654726330369191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 189290693275934990095752149 4436500623654726330369191)
      ·
        refine ⟨6654750935482089495553787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4436500623654726330369191 6654750935482089495553787)
        ·
          refine ⟨9982126403223134243330681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6654750935482089495553787 9982126403223134243330681)
          ·
            refine ⟨7486594802417350682498011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9982126403223134243330681 7486594802417350682498011)
            ·
              refine ⟨11229892203626026023747017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7486594802417350682498011 11229892203626026023747017)
              ·
                refine ⟨8422419152719519517810263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11229892203626026023747017 8422419152719519517810263)
                ·
                  refine ⟨12633628729079279276715395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8422419152719519517810263 12633628729079279276715395)
                  ·
                    refine ⟨18950443093618918915073093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12633628729079279276715395 18950443093618918915073093)
                    ·
                      refine ⟨3553208080053547296576205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18950443093618918915073093 3553208080053547296576205)
                      ·
                        rfl

theorem cell23_6919848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_6919848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6919848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6919848 prefixEnd_6919848 := by exact prefixLift 6919848
  have htrace : WordTrace (prefixWord ++ tailWord_6919848) baseStart_6919848 baseEnd_6919848 := by
    simpa [prefixWord, tailWord_6919848, baseEnd_6919848] using wordTrace_append hprefix tailTrace_6919848
  have hstable : (prefixWord ++ tailWord_6919848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6919848).length < 2 ^ (prefixWord ++ tailWord_6919848).sum := by decide
  have hdescent : baseEnd_6919848 < baseStart_6919848 := by decide
  rcases family_descends (prefixWord ++ tailWord_6919848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6919883 : List Nat := [1, 1, 1, 1, 3, 2, 1, 2, 3, 4, 4]
def baseStart_6919883 : Nat := 118140960795 + 6919883 * 2 ^ 59
def prefixEnd_6919883 : Nat := 4983230072969 + 3 ^ 40 * 6919883 * 2
def baseEnd_6919883 : Nat := 3553226051876454659638543

theorem tailTrace_6919883 : CollatzResearch.WordTrace tailWord_6919883 prefixEnd_6919883 3553226051876454659638543 := by
  unfold tailWord_6919883
  simp only [CollatzResearch.WordTrace]
  refine ⟨252388867589453187771860303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168259245059635458514573535 252388867589453187771860303)
  ·
    refine ⟨378583301384179781657790455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252388867589453187771860303 378583301384179781657790455)
    ·
      refine ⟨567874952076269672486685683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378583301384179781657790455 567874952076269672486685683)
      ·
        refine ⟨851812428114404508730028525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 567874952076269672486685683 851812428114404508730028525)
        ·
          refine ⟨319429660542901690773760697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 851812428114404508730028525 319429660542901690773760697)
          ·
            refine ⟨239572245407176268080320523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 319429660542901690773760697 239572245407176268080320523)
            ·
              refine ⟨359358368110764402120480785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239572245407176268080320523 359358368110764402120480785)
              ·
                refine ⟨269518776083073301590360589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 359358368110764402120480785 269518776083073301590360589)
                ·
                  refine ⟨101069541031152488096385221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 269518776083073301590360589 101069541031152488096385221)
                  ·
                    refine ⟨18950538943341091518072229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 101069541031152488096385221 18950538943341091518072229)
                    ·
                      refine ⟨3553226051876454659638543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18950538943341091518072229 3553226051876454659638543)
                      ·
                        rfl

theorem cell23_6919883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 4, 4].length) (baseStart_6919883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6919883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6919883 prefixEnd_6919883 := by exact prefixLift 6919883
  have htrace : WordTrace (prefixWord ++ tailWord_6919883) baseStart_6919883 baseEnd_6919883 := by
    simpa [prefixWord, tailWord_6919883, baseEnd_6919883] using wordTrace_append hprefix tailTrace_6919883
  have hstable : (prefixWord ++ tailWord_6919883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6919883).length < 2 ^ (prefixWord ++ tailWord_6919883).sum := by decide
  have hdescent : baseEnd_6919883 < baseStart_6919883 := by decide
  rcases family_descends (prefixWord ++ tailWord_6919883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6919887 : List Nat := [1, 1, 2, 1, 1, 3, 1, 5, 4, 2, 2]
def baseStart_6919887 : Nat := 118140960795 + 6919887 * 2 ^ 59
def prefixEnd_6919887 : Nat := 4983230072969 + 3 ^ 40 * 6919887 * 2
def baseEnd_6919887 : Nat := 3553228105799072643988525

theorem tailTrace_6919887 : CollatzResearch.WordTrace tailWord_6919887 prefixEnd_6919887 3553228105799072643988525 := by
  unfold tailWord_6919887
  simp only [CollatzResearch.WordTrace]
  refine ⟨252389013481438696455005915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168259342320959130970003943 252389013481438696455005915)
  ·
    refine ⟨378583520222158044682508873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252389013481438696455005915 378583520222158044682508873)
    ·
      refine ⟨283937640166618533511881655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 378583520222158044682508873 283937640166618533511881655)
      ·
        refine ⟨425906460249927800267822483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283937640166618533511881655 425906460249927800267822483)
        ·
          refine ⟨638859690374891700401733725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425906460249927800267822483 638859690374891700401733725)
          ·
            refine ⟨239572383890584387650650147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 638859690374891700401733725 239572383890584387650650147)
            ·
              refine ⟨359358575835876581475975221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239572383890584387650650147 359358575835876581475975221)
              ·
                refine ⟨33689866484613429513372677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 359358575835876581475975221 33689866484613429513372677)
                ·
                  refine ⟨6316849965865018033757377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33689866484613429513372677 6316849965865018033757377)
                  ·
                    refine ⟨4737637474398763525318033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6316849965865018033757377 4737637474398763525318033)
                    ·
                      refine ⟨3553228105799072643988525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4737637474398763525318033 3553228105799072643988525)
                      ·
                        rfl

theorem cell23_6919887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 4, 2, 2].length) (baseStart_6919887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6919887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6919887 prefixEnd_6919887 := by exact prefixLift 6919887
  have htrace : WordTrace (prefixWord ++ tailWord_6919887) baseStart_6919887 baseEnd_6919887 := by
    simpa [prefixWord, tailWord_6919887, baseEnd_6919887] using wordTrace_append hprefix tailTrace_6919887
  have hstable : (prefixWord ++ tailWord_6919887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6919887).length < 2 ^ (prefixWord ++ tailWord_6919887).sum := by decide
  have hdescent : baseEnd_6919887 < baseStart_6919887 := by decide
  rcases family_descends (prefixWord ++ tailWord_6919887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6919904 : List Nat := [2, 1, 1, 3, 1, 2, 4, 3, 2, 2, 2]
def baseStart_6919904 : Nat := 118140960795 + 6919904 * 2 ^ 59
def prefixEnd_6919904 : Nat := 4983230072969 + 3 ^ 40 * 6919904 * 2
def baseEnd_6919904 : Nat := 3553236834970199077475947

theorem tailTrace_6919904 : CollatzResearch.WordTrace tailWord_6919904 prefixEnd_6919904 3553236834970199077475947 := by
  unfold tailWord_6919904
  simp only [CollatzResearch.WordTrace]
  refine ⟨126194816761188554179187383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168259755681584738905583177 126194816761188554179187383)
  ·
    refine ⟨189292225141782831268781075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126194816761188554179187383 189292225141782831268781075)
    ·
      refine ⟨283938337712674246903171613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189292225141782831268781075 283938337712674246903171613)
      ·
        refine ⟨106476876642252842588689355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 283938337712674246903171613 106476876642252842588689355)
        ·
          refine ⟨159715314963379263883034033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106476876642252842588689355 159715314963379263883034033)
          ·
            refine ⟨119786486222534447912275525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159715314963379263883034033 119786486222534447912275525)
            ·
              refine ⟨22459966166725208983551661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119786486222534447912275525 22459966166725208983551661)
              ·
                refine ⟨8422487312521953368831873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22459966166725208983551661 8422487312521953368831873)
                ·
                  refine ⟨6316865484391465026623905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8422487312521953368831873 6316865484391465026623905)
                  ·
                    refine ⟨4737649113293598769967929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6316865484391465026623905 4737649113293598769967929)
                    ·
                      refine ⟨3553236834970199077475947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4737649113293598769967929 3553236834970199077475947)
                      ·
                        rfl

theorem cell23_6919904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 3, 2, 2, 2].length) (baseStart_6919904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6919904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6919904 prefixEnd_6919904 := by exact prefixLift 6919904
  have htrace : WordTrace (prefixWord ++ tailWord_6919904) baseStart_6919904 baseEnd_6919904 := by
    simpa [prefixWord, tailWord_6919904, baseEnd_6919904] using wordTrace_append hprefix tailTrace_6919904
  have hstable : (prefixWord ++ tailWord_6919904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6919904).length < 2 ^ (prefixWord ++ tailWord_6919904).sum := by decide
  have hdescent : baseEnd_6919904 < baseStart_6919904 := by decide
  rcases family_descends (prefixWord ++ tailWord_6919904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6919950 : List Nat := [4, 1, 1, 2, 1, 1, 2, 3, 1, 2, 5]
def baseStart_6919950 : Nat := 118140960795 + 6919950 * 2 ^ 59
def prefixEnd_6919950 : Nat := 4983230072969 + 3 ^ 40 * 6919950 * 2
def baseEnd_6919950 : Nat := 3553260455080305897500735

theorem tailTrace_6919950 : CollatzResearch.WordTrace tailWord_6919950 prefixEnd_6919950 3553260455080305897500735 := by
  unfold tailWord_6919950
  simp only [CollatzResearch.WordTrace]
  refine ⟨31548913910026307276818663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168260874186806972143032869 31548913910026307276818663)
  ·
    refine ⟨47323370865039460915227995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31548913910026307276818663 47323370865039460915227995)
    ·
      refine ⟨70985056297559191372841993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47323370865039460915227995 70985056297559191372841993)
      ·
        refine ⟨53238792223169393529631495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70985056297559191372841993 53238792223169393529631495)
        ·
          refine ⟨79858188334754090294447243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53238792223169393529631495 79858188334754090294447243)
          ·
            refine ⟨119787282502131135441670865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79858188334754090294447243 119787282502131135441670865)
            ·
              refine ⟨89840461876598351581253149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119787282502131135441670865 89840461876598351581253149)
              ·
                refine ⟨33690173203724381842969931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89840461876598351581253149 33690173203724381842969931)
                ·
                  refine ⟨50535259805586572764454897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33690173203724381842969931 50535259805586572764454897)
                  ·
                    refine ⟨37901444854189929573341173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50535259805586572764454897 37901444854189929573341173)
                    ·
                      refine ⟨3553260455080305897500735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37901444854189929573341173 3553260455080305897500735)
                      ·
                        rfl

theorem cell23_6919950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_6919950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6919950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6919950 prefixEnd_6919950 := by exact prefixLift 6919950
  have htrace : WordTrace (prefixWord ++ tailWord_6919950) baseStart_6919950 baseEnd_6919950 := by
    simpa [prefixWord, tailWord_6919950, baseEnd_6919950] using wordTrace_append hprefix tailTrace_6919950
  have hstable : (prefixWord ++ tailWord_6919950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6919950).length < 2 ^ (prefixWord ++ tailWord_6919950).sum := by decide
  have hdescent : baseEnd_6919950 < baseStart_6919950 := by decide
  rcases family_descends (prefixWord ++ tailWord_6919950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6919954 : List Nat := [3, 2, 4, 1, 1, 1, 2, 1, 2, 3, 3]
def baseStart_6919954 : Nat := 118140960795 + 6919954 * 2 ^ 59
def prefixEnd_6919954 : Nat := 4983230072969 + 3 ^ 40 * 6919954 * 2
def baseEnd_6919954 : Nat := 3553262509002923881850717

theorem tailTrace_6919954 : CollatzResearch.WordTrace tailWord_6919954 prefixEnd_6919954 3553262509002923881850717 := by
  unfold tailWord_6919954
  simp only [CollatzResearch.WordTrace]
  refine ⟨63097864293048991724423729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168260971448130644598463277 63097864293048991724423729)
  ·
    refine ⟨47323398219786743793317797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63097864293048991724423729 47323398219786743793317797)
    ·
      refine ⟨8873137166210014461247087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47323398219786743793317797 8873137166210014461247087)
      ·
        refine ⟨13309705749315021691870631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8873137166210014461247087 13309705749315021691870631)
        ·
          refine ⟨19964558623972532537805947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13309705749315021691870631 19964558623972532537805947)
          ·
            refine ⟨29946837935958798806708921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19964558623972532537805947 29946837935958798806708921)
            ·
              refine ⟨22460128451969099105031691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29946837935958798806708921 22460128451969099105031691)
              ·
                refine ⟨33690192677953648657547537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22460128451969099105031691 33690192677953648657547537)
                ·
                  refine ⟨25267644508465236493160653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33690192677953648657547537 25267644508465236493160653)
                  ·
                    refine ⟨9475366690674463684935245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25267644508465236493160653 9475366690674463684935245)
                    ·
                      refine ⟨3553262509002923881850717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9475366690674463684935245 3553262509002923881850717)
                      ·
                        rfl

theorem cell23_6919954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_6919954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6919954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6919954 prefixEnd_6919954 := by exact prefixLift 6919954
  have htrace : WordTrace (prefixWord ++ tailWord_6919954) baseStart_6919954 baseEnd_6919954 := by
    simpa [prefixWord, tailWord_6919954, baseEnd_6919954] using wordTrace_append hprefix tailTrace_6919954
  have hstable : (prefixWord ++ tailWord_6919954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6919954).length < 2 ^ (prefixWord ++ tailWord_6919954).sum := by decide
  have hdescent : baseEnd_6919954 < baseStart_6919954 := by decide
  rcases family_descends (prefixWord ++ tailWord_6919954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6919960 : List Nat := [2, 1, 2, 3, 1, 1, 3, 2, 1, 3, 4]
def baseStart_6919960 : Nat := 118140960795 + 6919960 * 2 ^ 59
def prefixEnd_6919960 : Nat := 4983230072969 + 3 ^ 40 * 6919960 * 2
def baseEnd_6919960 : Nat := 3553265589886850858375689

theorem tailTrace_6919960 : CollatzResearch.WordTrace tailWord_6919960 prefixEnd_6919960 3553265589886850858375689 := by
  unfold tailWord_6919960
  simp only [CollatzResearch.WordTrace]
  refine ⟨126195838005087114961206667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168261117340116153281608889 126195838005087114961206667)
  ·
    refine ⟨189293757007630672441810001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126195838005087114961206667 189293757007630672441810001)
    ·
      refine ⟨141970317755723004331357501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189293757007630672441810001 141970317755723004331357501)
      ·
        refine ⟨53238869158396126624259063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141970317755723004331357501 53238869158396126624259063)
        ·
          refine ⟨79858303737594189936388595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53238869158396126624259063 79858303737594189936388595)
          ·
            refine ⟨119787455606391284904582893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79858303737594189936388595 119787455606391284904582893)
            ·
              refine ⟨44920295852396731839218585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119787455606391284904582893 44920295852396731839218585)
              ·
                refine ⟨33690221889297548879413939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44920295852396731839218585 33690221889297548879413939)
                ·
                  refine ⟨50535332833946323319120909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33690221889297548879413939 50535332833946323319120909)
                  ·
                    refine ⟨18950749812729871244670341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50535332833946323319120909 18950749812729871244670341)
                    ·
                      refine ⟨3553265589886850858375689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18950749812729871244670341 3553265589886850858375689)
                      ·
                        rfl

theorem cell23_6919960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_6919960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6919960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6919960 prefixEnd_6919960 := by exact prefixLift 6919960
  have htrace : WordTrace (prefixWord ++ tailWord_6919960) baseStart_6919960 baseEnd_6919960 := by
    simpa [prefixWord, tailWord_6919960, baseEnd_6919960] using wordTrace_append hprefix tailTrace_6919960
  have hstable : (prefixWord ++ tailWord_6919960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6919960).length < 2 ^ (prefixWord ++ tailWord_6919960).sum := by decide
  have hdescent : baseEnd_6919960 < baseStart_6919960 := by decide
  rcases family_descends (prefixWord ++ tailWord_6919960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6919970 : List Nat := [3, 3, 1, 1, 2, 1, 1, 1, 2, 8]
def baseStart_6919970 : Nat := 118140960795 + 6919970 * 2 ^ 59
def prefixEnd_6919970 : Nat := 4983230072969 + 3 ^ 40 * 6919970 * 2
def baseEnd_6919970 : Nat := 1184423574897798606416881

theorem tailTrace_6919970 : CollatzResearch.WordTrace tailWord_6919970 prefixEnd_6919970 1184423574897798606416881 := by
  unfold tailWord_6919970
  simp only [CollatzResearch.WordTrace]
  refine ⟨63098010185034500407569341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168261360493425334420184909 63098010185034500407569341)
  ·
    refine ⟨23661753819387937652838503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63098010185034500407569341 23661753819387937652838503)
    ·
      refine ⟨35492630729081906479257755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23661753819387937652838503 35492630729081906479257755)
      ·
        refine ⟨53238946093622859718886633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35492630729081906479257755 53238946093622859718886633)
        ·
          refine ⟨39929209570217144789164975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53238946093622859718886633 39929209570217144789164975)
          ·
            refine ⟨59893814355325717183747463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39929209570217144789164975 59893814355325717183747463)
            ·
              refine ⟨89840721532988575775621195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59893814355325717183747463 89840721532988575775621195)
              ·
                refine ⟨134761082299482863663431793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89840721532988575775621195 134761082299482863663431793)
                ·
                  refine ⟨101070811724612147747573845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134761082299482863663431793 101070811724612147747573845)
                  ·
                    refine ⟨1184423574897798606416881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 101070811724612147747573845 1184423574897798606416881)
                    ·
                      rfl

theorem cell23_6919970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_6919970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6919970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6919970 prefixEnd_6919970 := by exact prefixLift 6919970
  have htrace : WordTrace (prefixWord ++ tailWord_6919970) baseStart_6919970 baseEnd_6919970 := by
    simpa [prefixWord, tailWord_6919970, baseEnd_6919970] using wordTrace_append hprefix tailTrace_6919970
  have hstable : (prefixWord ++ tailWord_6919970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6919970).length < 2 ^ (prefixWord ++ tailWord_6919970).sum := by decide
  have hdescent : baseEnd_6919970 < baseStart_6919970 := by decide
  rcases family_descends (prefixWord ++ tailWord_6919970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6920017 : List Nat := [1, 2, 2, 1, 5, 2, 1, 3, 6]
def baseStart_6920017 : Nat := 118140960795 + 6920017 * 2 ^ 59
def prefixEnd_6920017 : Nat := 4983230072969 + 3 ^ 40 * 6920017 * 2
def baseEnd_6920017 : Nat := 394810539809350792818103

theorem tailTrace_6920017 : CollatzResearch.WordTrace tailWord_6920017 prefixEnd_6920017 394810539809350792818103 := by
  unfold tailWord_6920017
  simp only [CollatzResearch.WordTrace]
  refine ⟨252393754970967728657238305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168262503313978485771492203 252393754970967728657238305)
  ·
    refine ⟨189295316228225796492928729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252393754970967728657238305 189295316228225796492928729)
    ·
      refine ⟨141971487171169347369696547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189295316228225796492928729 141971487171169347369696547)
      ·
        refine ⟨212957230756754021054544821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141971487171169347369696547 212957230756754021054544821)
        ·
          refine ⟨19964740383445689473863577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 212957230756754021054544821 19964740383445689473863577)
          ·
            refine ⟨14973555287584267105397683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19964740383445689473863577 14973555287584267105397683)
            ·
              refine ⟨22460332931376400658096525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14973555287584267105397683 22460332931376400658096525)
              ·
                refine ⟨8422624849266150246786197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22460332931376400658096525 8422624849266150246786197)
                ·
                  refine ⟨394810539809350792818103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8422624849266150246786197 394810539809350792818103)
                  ·
                    rfl

theorem cell23_6920017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 3, 6].length) (baseStart_6920017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6920017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6920017 prefixEnd_6920017 := by exact prefixLift 6920017
  have htrace : WordTrace (prefixWord ++ tailWord_6920017) baseStart_6920017 baseEnd_6920017 := by
    simpa [prefixWord, tailWord_6920017, baseEnd_6920017] using wordTrace_append hprefix tailTrace_6920017
  have hstable : (prefixWord ++ tailWord_6920017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6920017).length < 2 ^ (prefixWord ++ tailWord_6920017).sum := by decide
  have hdescent : baseEnd_6920017 < baseStart_6920017 := by decide
  rcases family_descends (prefixWord ++ tailWord_6920017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6920067 : List Nat := [1, 1, 1, 3, 4, 2, 1, 2, 3, 1, 4]
def baseStart_6920067 : Nat := 118140960795 + 6920067 * 2 ^ 59
def prefixEnd_6920067 : Nat := 4983230072969 + 3 ^ 40 * 6920067 * 2
def baseEnd_6920067 : Nat := 3553320532316881939737697

theorem tailTrace_6920067 : CollatzResearch.WordTrace tailWord_6920067 prefixEnd_6920067 3553320532316881939737697 := by
  unfold tailWord_6920067
  simp only [CollatzResearch.WordTrace]
  refine ⟨252395578620786587196558455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168263719080524391464372303 252395578620786587196558455)
  ·
    refine ⟨378593367931179880794837683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252395578620786587196558455 378593367931179880794837683)
    ·
      refine ⟨567890051896769821192256525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378593367931179880794837683 567890051896769821192256525)
      ·
        refine ⟨212958769461288682947096197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 567890051896769821192256525 212958769461288682947096197)
        ·
          refine ⟨39929769273991628052580537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 212958769461288682947096197 39929769273991628052580537)
          ·
            refine ⟨29947326955493721039435403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39929769273991628052580537 29947326955493721039435403)
            ·
              refine ⟨44920990433240581559153105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29947326955493721039435403 44920990433240581559153105)
              ·
                refine ⟨33690742824930436169364829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44920990433240581559153105 33690742824930436169364829)
                ·
                  refine ⟨12634028559348913563511811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33690742824930436169364829 12634028559348913563511811)
                  ·
                    refine ⟨18951042839023370345267717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12634028559348913563511811 18951042839023370345267717)
                    ·
                      refine ⟨3553320532316881939737697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18951042839023370345267717 3553320532316881939737697)
                      ·
                        rfl

theorem cell23_6920067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 3, 1, 4].length) (baseStart_6920067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6920067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6920067 prefixEnd_6920067 := by exact prefixLift 6920067
  have htrace : WordTrace (prefixWord ++ tailWord_6920067) baseStart_6920067 baseEnd_6920067 := by
    simpa [prefixWord, tailWord_6920067, baseEnd_6920067] using wordTrace_append hprefix tailTrace_6920067
  have hstable : (prefixWord ++ tailWord_6920067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6920067).length < 2 ^ (prefixWord ++ tailWord_6920067).sum := by decide
  have hdescent : baseEnd_6920067 < baseStart_6920067 := by decide
  rcases family_descends (prefixWord ++ tailWord_6920067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6920078 : List Nat := [4, 1, 1, 5, 1, 1, 1, 2, 3, 1, 3]
def baseStart_6920078 : Nat := 118140960795 + 6920078 * 2 ^ 59
def prefixEnd_6920078 : Nat := 4983230072969 + 3 ^ 40 * 6920078 * 2
def baseEnd_6920078 : Nat := 3553326180604081396700147

theorem tailTrace_6920078 : CollatzResearch.WordTrace tailWord_6920078 prefixEnd_6920078 3553326180604081396700147 := by
  unfold tailWord_6920078
  simp only [CollatzResearch.WordTrace]
  refine ⟨31549497477968342009401111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168263986549164490716805925 31549497477968342009401111)
  ·
    refine ⟨47324246216952513014101667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31549497477968342009401111 47324246216952513014101667)
    ·
      refine ⟨70986369325428769521152501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47324246216952513014101667 70986369325428769521152501)
      ·
        refine ⟨6654972124258947142608047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70986369325428769521152501 6654972124258947142608047)
        ·
          refine ⟨9982458186388420713912071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6654972124258947142608047 9982458186388420713912071)
          ·
            refine ⟨14973687279582631070868107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9982458186388420713912071 14973687279582631070868107)
            ·
              refine ⟨22460530919373946606302161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14973687279582631070868107 22460530919373946606302161)
              ·
                refine ⟨16845398189530459954726621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22460530919373946606302161 16845398189530459954726621)
                ·
                  refine ⟨6317024321073922483022483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16845398189530459954726621 6317024321073922483022483)
                  ·
                    refine ⟨9475536481610883724533725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6317024321073922483022483 9475536481610883724533725)
                    ·
                      refine ⟨3553326180604081396700147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9475536481610883724533725 3553326180604081396700147)
                      ·
                        rfl

theorem cell23_6920078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_6920078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6920078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6920078 prefixEnd_6920078 := by exact prefixLift 6920078
  have htrace : WordTrace (prefixWord ++ tailWord_6920078) baseStart_6920078 baseEnd_6920078 := by
    simpa [prefixWord, tailWord_6920078, baseEnd_6920078] using wordTrace_append hprefix tailTrace_6920078
  have hstable : (prefixWord ++ tailWord_6920078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6920078).length < 2 ^ (prefixWord ++ tailWord_6920078).sum := by decide
  have hdescent : baseEnd_6920078 < baseStart_6920078 := by decide
  rcases family_descends (prefixWord ++ tailWord_6920078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6920084 : List Nat := [2, 4, 2, 1, 1, 2, 2, 1, 3, 1, 4]
def baseStart_6920084 : Nat := 118140960795 + 6920084 * 2 ^ 59
def prefixEnd_6920084 : Nat := 4983230072969 + 3 ^ 40 * 6920084 * 2
def baseEnd_6920084 : Nat := 3553329261488008373225119

theorem tailTrace_6920084 : CollatzResearch.WordTrace tailWord_6920084 prefixEnd_6920084 3553329261488008373225119 := by
  unfold tailWord_6920084
  simp only [CollatzResearch.WordTrace]
  refine ⟨126198099330862499549963653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168264132441149999399951537 126198099330862499549963653)
  ·
    refine ⟨23662143624536718665618185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126198099330862499549963653 23662143624536718665618185)
    ·
      refine ⟨17746607718402538999213639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23662143624536718665618185 17746607718402538999213639)
      ·
        refine ⟨26619911577603808498820459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17746607718402538999213639 26619911577603808498820459)
        ·
          refine ⟨39929867366405712748230689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26619911577603808498820459 39929867366405712748230689)
          ·
            refine ⟨29947400524804284561173017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39929867366405712748230689 29947400524804284561173017)
            ·
              refine ⟨22460550393603213420879763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29947400524804284561173017 22460550393603213420879763)
              ·
                refine ⟨33690825590404820131319645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22460550393603213420879763 33690825590404820131319645)
                ·
                  refine ⟨12634059596401807549244867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33690825590404820131319645 12634059596401807549244867)
                  ·
                    refine ⟨18951089394602711323867301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12634059596401807549244867 18951089394602711323867301)
                    ·
                      refine ⟨3553329261488008373225119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18951089394602711323867301 3553329261488008373225119)
                      ·
                        rfl

theorem cell23_6920084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_6920084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6920084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6920084 prefixEnd_6920084 := by exact prefixLift 6920084
  have htrace : WordTrace (prefixWord ++ tailWord_6920084) baseStart_6920084 baseEnd_6920084 := by
    simpa [prefixWord, tailWord_6920084, baseEnd_6920084] using wordTrace_append hprefix tailTrace_6920084
  have hstable : (prefixWord ++ tailWord_6920084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6920084).length < 2 ^ (prefixWord ++ tailWord_6920084).sum := by decide
  have hdescent : baseEnd_6920084 < baseStart_6920084 := by decide
  rcases family_descends (prefixWord ++ tailWord_6920084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6920098 : List Nat := [3, 3, 1, 2, 3, 2, 2, 1, 1, 5]
def baseStart_6920098 : Nat := 118140960795 + 6920098 * 2 ^ 59
def prefixEnd_6920098 : Nat := 4983230072969 + 3 ^ 40 * 6920098 * 2
def baseEnd_6920098 : Nat := 1184445483405723772816685

theorem tailTrace_6920098 : CollatzResearch.WordTrace tailWord_6920098 prefixEnd_6920098 1184445483405723772816685 := by
  unfold tailWord_6920098
  simp only [CollatzResearch.WordTrace]
  refine ⟨63099177320918569872734237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168264472855782852993957965 63099177320918569872734237)
  ·
    refine ⟨23662191495344463702275339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63099177320918569872734237 23662191495344463702275339)
    ·
      refine ⟨35493287243016695553413009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23662191495344463702275339 35493287243016695553413009)
      ·
        refine ⟨26619965432262521665059757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35493287243016695553413009 26619965432262521665059757)
        ·
          refine ⟨9982487037098445624397409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26619965432262521665059757 9982487037098445624397409)
          ·
            refine ⟨7486865277823834218298057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9982487037098445624397409 7486865277823834218298057)
            ·
              refine ⟨5615148958367875663723543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7486865277823834218298057 5615148958367875663723543)
              ·
                refine ⟨8422723437551813495585315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5615148958367875663723543 8422723437551813495585315)
                ·
                  refine ⟨12634085156327720243377973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8422723437551813495585315 12634085156327720243377973)
                  ·
                    refine ⟨1184445483405723772816685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12634085156327720243377973 1184445483405723772816685)
                    ·
                      rfl

theorem cell23_6920098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 2, 1, 1, 5].length) (baseStart_6920098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6920098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6920098 prefixEnd_6920098 := by exact prefixLift 6920098
  have htrace : WordTrace (prefixWord ++ tailWord_6920098) baseStart_6920098 baseEnd_6920098 := by
    simpa [prefixWord, tailWord_6920098, baseEnd_6920098] using wordTrace_append hprefix tailTrace_6920098
  have hstable : (prefixWord ++ tailWord_6920098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6920098).length < 2 ^ (prefixWord ++ tailWord_6920098).sum := by decide
  have hdescent : baseEnd_6920098 < baseStart_6920098 := by decide
  rcases family_descends (prefixWord ++ tailWord_6920098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6920144 : List Nat := [2, 1, 1, 1, 1, 2, 4, 3, 3, 3, 2]
def baseStart_6920144 : Nat := 118140960795 + 6920144 * 2 ^ 59
def prefixEnd_6920144 : Nat := 4983230072969 + 3 ^ 40 * 6920144 * 2
def baseEnd_6920144 : Nat := 3553360070327278138474843

theorem tailTrace_6920144 : CollatzResearch.WordTrace tailWord_6920144 prefixEnd_6920144 3553360070327278138474843 := by
  unfold tailWord_6920144
  simp only [CollatzResearch.WordTrace]
  refine ⟨126199193520753814673555743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168265591361005086231407657 126199193520753814673555743)
  ·
    refine ⟨189298790281130722010333615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126199193520753814673555743 189298790281130722010333615)
    ·
      refine ⟨283948185421696083015500423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189298790281130722010333615 283948185421696083015500423)
      ·
        refine ⟨425922278132544124523250635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283948185421696083015500423 425922278132544124523250635)
        ·
          refine ⟨638883417198816186784875953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425922278132544124523250635 638883417198816186784875953)
          ·
            refine ⟨479162562899112140088656965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 638883417198816186784875953 479162562899112140088656965)
            ·
              refine ⟨89842980543583526266623181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 479162562899112140088656965 89842980543583526266623181)
              ·
                refine ⟨33691117703843822349983693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89842980543583526266623181 33691117703843822349983693)
                ·
                  refine ⟨12634169138941433381243885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33691117703843822349983693 12634169138941433381243885)
                  ·
                    refine ⟨4737813427103037517966457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12634169138941433381243885 4737813427103037517966457)
                    ·
                      refine ⟨3553360070327278138474843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4737813427103037517966457 3553360070327278138474843)
                      ·
                        rfl

theorem cell23_6920144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 3, 3, 2].length) (baseStart_6920144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6920144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6920144 prefixEnd_6920144 := by exact prefixLift 6920144
  have htrace : WordTrace (prefixWord ++ tailWord_6920144) baseStart_6920144 baseEnd_6920144 := by
    simpa [prefixWord, tailWord_6920144, baseEnd_6920144] using wordTrace_append hprefix tailTrace_6920144
  have hstable : (prefixWord ++ tailWord_6920144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6920144).length < 2 ^ (prefixWord ++ tailWord_6920144).sum := by decide
  have hdescent : baseEnd_6920144 < baseStart_6920144 := by decide
  rcases family_descends (prefixWord ++ tailWord_6920144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6920161 : List Nat := [1, 2, 3, 1, 2, 1, 4, 3, 1, 3, 2]
def baseStart_6920161 : Nat := 118140960795 + 6920161 * 2 ^ 59
def prefixEnd_6920161 : Nat := 4983230072969 + 3 ^ 40 * 6920161 * 2
def baseEnd_6920161 : Nat := 3553368799498404571962265

theorem tailTrace_6920161 : CollatzResearch.WordTrace tailWord_6920161 prefixEnd_6920161 3553368799498404571962265 := by
  unfold tailWord_6920161
  simp only [CollatzResearch.WordTrace]
  refine ⟨252399007082446041250480337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168266004721630694166986891 252399007082446041250480337)
  ·
    refine ⟨189299255311834530937860253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252399007082446041250480337 189299255311834530937860253)
    ·
      refine ⟨70987220741937949101697595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189299255311834530937860253 70987220741937949101697595)
      ·
        refine ⟨106480831112906923652546393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70987220741937949101697595 106480831112906923652546393)
        ·
          refine ⟨79860623334680192739409795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106480831112906923652546393 79860623334680192739409795)
          ·
            refine ⟨119790935002020289109114693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79860623334680192739409795 119790935002020289109114693)
            ·
              refine ⟨22460800312878804207959005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119790935002020289109114693 22460800312878804207959005)
              ·
                refine ⟨8422800117329551577984627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22460800312878804207959005 8422800117329551577984627)
                ·
                  refine ⟨12634200175994327366976941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8422800117329551577984627 12634200175994327366976941)
                  ·
                    refine ⟨4737825065997872762616353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12634200175994327366976941 4737825065997872762616353)
                    ·
                      refine ⟨3553368799498404571962265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4737825065997872762616353 3553368799498404571962265)
                      ·
                        rfl

theorem cell23_6920161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 3, 1, 3, 2].length) (baseStart_6920161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6920161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6920161 prefixEnd_6920161 := by exact prefixLift 6920161
  have htrace : WordTrace (prefixWord ++ tailWord_6920161) baseStart_6920161 baseEnd_6920161 := by
    simpa [prefixWord, tailWord_6920161, baseEnd_6920161] using wordTrace_append hprefix tailTrace_6920161
  have hstable : (prefixWord ++ tailWord_6920161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6920161).length < 2 ^ (prefixWord ++ tailWord_6920161).sum := by decide
  have hdescent : baseEnd_6920161 < baseStart_6920161 := by decide
  rcases family_descends (prefixWord ++ tailWord_6920161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6920187 : List Nat := [1, 1, 1, 1, 1, 3, 4, 3, 2, 2, 4]
def baseStart_6920187 : Nat := 118140960795 + 6920187 * 2 ^ 59
def prefixEnd_6920187 : Nat := 4983230072969 + 3 ^ 40 * 6920187 * 2
def baseEnd_6920187 : Nat := 3553382149995421470237145

theorem tailTrace_6920187 : CollatzResearch.WordTrace tailWord_6920187 prefixEnd_6920187 3553382149995421470237145 := by
  unfold tailWord_6920187
  simp only [CollatzResearch.WordTrace]
  refine ⟨252399955380351847690926815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168266636920234565127284543 252399955380351847690926815)
  ·
    refine ⟨378599933070527771536390223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252399955380351847690926815 378599933070527771536390223)
    ·
      refine ⟨567899899605791657304585335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378599933070527771536390223 567899899605791657304585335)
      ·
        refine ⟨851849849408687485956878003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 567899899605791657304585335 851849849408687485956878003)
        ·
          refine ⟨1277774774113031228935317005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 851849849408687485956878003 1277774774113031228935317005)
          ·
            refine ⟨479165540292386710850743877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1277774774113031228935317005 479165540292386710850743877)
            ·
              refine ⟨89843538804822508284514477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 479165540292386710850743877 89843538804822508284514477)
              ·
                refine ⟨33691327051808440606692929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89843538804822508284514477 33691327051808440606692929)
                ·
                  refine ⟨25268495288856330455019697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33691327051808440606692929 25268495288856330455019697)
                  ·
                    refine ⟨18951371466642247841264773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25268495288856330455019697 18951371466642247841264773)
                    ·
                      refine ⟨3553382149995421470237145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18951371466642247841264773 3553382149995421470237145)
                      ·
                        rfl

theorem cell23_6920187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 2, 2, 4].length) (baseStart_6920187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6920187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6920187 prefixEnd_6920187 := by exact prefixLift 6920187
  have htrace : WordTrace (prefixWord ++ tailWord_6920187) baseStart_6920187 baseEnd_6920187 := by
    simpa [prefixWord, tailWord_6920187, baseEnd_6920187] using wordTrace_append hprefix tailTrace_6920187
  have hstable : (prefixWord ++ tailWord_6920187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6920187).length < 2 ^ (prefixWord ++ tailWord_6920187).sum := by decide
  have hdescent : baseEnd_6920187 < baseStart_6920187 := by decide
  rcases family_descends (prefixWord ++ tailWord_6920187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6920225 : List Nat := [1, 2, 3, 2, 4, 1, 2, 2, 2, 2, 2]
def baseStart_6920225 : Nat := 118140960795 + 6920225 * 2 ^ 59
def prefixEnd_6920225 : Nat := 4983230072969 + 3 ^ 40 * 6920225 * 2
def baseEnd_6920225 : Nat := 3553401662260292321561971

theorem tailTrace_6920225 : CollatzResearch.WordTrace tailWord_6920225 prefixEnd_6920225 3553401662260292321561971 := by
  unfold tailWord_6920225
  simp only [CollatzResearch.WordTrace]
  refine ⟨252401341354214180180810129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168267560902809453453873419 252401341354214180180810129)
  ·
    refine ⟨189301006015660635135607597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252401341354214180180810129 189301006015660635135607597)
    ·
      refine ⟨70987877255872738175852849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189301006015660635135607597 70987877255872738175852849)
      ·
        refine ⟨53240907941904553631889637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70987877255872738175852849 53240907941904553631889637)
        ·
          refine ⟨9982670239107103805979307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53240907941904553631889637 9982670239107103805979307)
          ·
            refine ⟨14974005358660655708968961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9982670239107103805979307 14974005358660655708968961)
            ·
              refine ⟨11230504018995491781726721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14974005358660655708968961 11230504018995491781726721)
              ·
                refine ⟨8422878014246618836295041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11230504018995491781726721 8422878014246618836295041)
                ·
                  refine ⟨6317158510684964127221281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8422878014246618836295041 6317158510684964127221281)
                  ·
                    refine ⟨4737868883013723095415961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6317158510684964127221281 4737868883013723095415961)
                    ·
                      refine ⟨3553401662260292321561971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4737868883013723095415961 3553401662260292321561971)
                      ·
                        rfl

theorem cell23_6920225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 2, 2, 2, 2].length) (baseStart_6920225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6920225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6920225 prefixEnd_6920225 := by exact prefixLift 6920225
  have htrace : WordTrace (prefixWord ++ tailWord_6920225) baseStart_6920225 baseEnd_6920225 := by
    simpa [prefixWord, tailWord_6920225, baseEnd_6920225] using wordTrace_append hprefix tailTrace_6920225
  have hstable : (prefixWord ++ tailWord_6920225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6920225).length < 2 ^ (prefixWord ++ tailWord_6920225).sum := by decide
  have hdescent : baseEnd_6920225 < baseStart_6920225 := by decide
  rcases family_descends (prefixWord ++ tailWord_6920225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6920264 : List Nat := [2, 1, 3, 1, 1, 1, 2, 5, 2, 1, 4]
def baseStart_6920264 : Nat := 118140960795 + 6920264 * 2 ^ 59
def prefixEnd_6920264 : Nat := 4983230072969 + 3 ^ 40 * 6920264 * 2
def baseEnd_6920264 : Nat := 3553421688005817668974291

theorem tailTrace_6920264 : CollatzResearch.WordTrace tailWord_6920264 prefixEnd_6920264 3553421688005817668974291 := by
  unfold tailWord_6920264
  simp only [CollatzResearch.WordTrace]
  refine ⟨126201381900536444920739923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168268509200715259894319897 126201381900536444920739923)
  ·
    refine ⟨189302072850804667381109885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126201381900536444920739923 189302072850804667381109885)
    ·
      refine ⟨70988277319051750267916207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189302072850804667381109885 70988277319051750267916207)
      ·
        refine ⟨106482415978577625401874311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70988277319051750267916207 106482415978577625401874311)
        ·
          refine ⟨159723623967866438102811467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106482415978577625401874311 159723623967866438102811467)
          ·
            refine ⟨239585435951799657154217201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159723623967866438102811467 239585435951799657154217201)
            ·
              refine ⟨179689076963849742865662901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 239585435951799657154217201 179689076963849742865662901)
              ·
                refine ⟨16845850965360913393655897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 179689076963849742865662901 16845850965360913393655897)
                ·
                  refine ⟨12634388224020685045241923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16845850965360913393655897 12634388224020685045241923)
                  ·
                    refine ⟨18951582336031027567862885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12634388224020685045241923 18951582336031027567862885)
                    ·
                      refine ⟨3553421688005817668974291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18951582336031027567862885 3553421688005817668974291)
                      ·
                        rfl

theorem cell23_6920264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 5, 2, 1, 4].length) (baseStart_6920264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6920264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6920264 prefixEnd_6920264 := by exact prefixLift 6920264
  have htrace : WordTrace (prefixWord ++ tailWord_6920264) baseStart_6920264 baseEnd_6920264 := by
    simpa [prefixWord, tailWord_6920264, baseEnd_6920264] using wordTrace_append hprefix tailTrace_6920264
  have hstable : (prefixWord ++ tailWord_6920264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6920264).length < 2 ^ (prefixWord ++ tailWord_6920264).sum := by decide
  have hdescent : baseEnd_6920264 < baseStart_6920264 := by decide
  rcases family_descends (prefixWord ++ tailWord_6920264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6920325 : List Nat := [1, 3, 1, 1, 5, 3, 1, 3, 1, 4]
def baseStart_6920325 : Nat := 118140960795 + 6920325 * 2 ^ 59
def prefixEnd_6920325 : Nat := 4983230072969 + 3 ^ 40 * 6920325 * 2
def baseEnd_6920325 : Nat := 1184484336775247310103837

theorem tailTrace_6920325 : CollatzResearch.WordTrace tailWord_6920325 prefixEnd_6920325 1184484336775247310103837 := by
  unfold tailWord_6920325
  simp only [CollatzResearch.WordTrace]
  refine ⟨252404988653851897259450429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168269992435901264839633619 252404988653851897259450429)
  ·
    refine ⟨94651870745194461472293911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252404988653851897259450429 94651870745194461472293911)
    ·
      refine ⟨141977806117791692208440867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94651870745194461472293911 141977806117791692208440867)
      ·
        refine ⟨212966709176687538312661301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141977806117791692208440867 212966709176687538312661301)
        ·
          refine ⟨19965628985314456716811997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 212966709176687538312661301 19965628985314456716811997)
          ·
            refine ⟨7487110869492921268804499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19965628985314456716811997 7487110869492921268804499)
            ·
              refine ⟨11230666304239381903206749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7487110869492921268804499 11230666304239381903206749)
              ·
                refine ⟨4211499864089768213702531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11230666304239381903206749 4211499864089768213702531)
                ·
                  refine ⟨6317249796134652320553797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4211499864089768213702531 6317249796134652320553797)
                  ·
                    refine ⟨1184484336775247310103837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6317249796134652320553797 1184484336775247310103837)
                    ·
                      rfl

theorem cell23_6920325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 3, 1, 4].length) (baseStart_6920325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6920325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6920325 prefixEnd_6920325 := by exact prefixLift 6920325
  have htrace : WordTrace (prefixWord ++ tailWord_6920325) baseStart_6920325 baseEnd_6920325 := by
    simpa [prefixWord, tailWord_6920325, baseEnd_6920325] using wordTrace_append hprefix tailTrace_6920325
  have hstable : (prefixWord ++ tailWord_6920325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6920325).length < 2 ^ (prefixWord ++ tailWord_6920325).sum := by decide
  have hdescent : baseEnd_6920325 < baseStart_6920325 := by decide
  rcases family_descends (prefixWord ++ tailWord_6920325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6920398 : List Nat := [4, 1, 1, 1, 4, 1, 1, 4, 2, 4]
def baseStart_6920398 : Nat := 118140960795 + 6920398 * 2 ^ 59
def prefixEnd_6920398 : Nat := 4983230072969 + 3 ^ 40 * 6920398 * 2
def baseEnd_6920398 : Nat := 1184496831471173381566225

theorem tailTrace_6920398 : CollatzResearch.WordTrace tailWord_6920398 prefixEnd_6920398 1184496831471173381566225 := by
  unfold tailWord_6920398
  simp only [CollatzResearch.WordTrace]
  refine ⟨31550956397823428840857231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168271767455058287151238565 31550956397823428840857231)
  ·
    refine ⟨47326434596735143261285847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31550956397823428840857231 47326434596735143261285847)
    ·
      refine ⟨70989651895102714891928771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47326434596735143261285847 70989651895102714891928771)
      ·
        refine ⟨106484477842654072337893157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70989651895102714891928771 106484477842654072337893157)
        ·
          refine ⟨19965839595497638563354967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106484477842654072337893157 19965839595497638563354967)
          ·
            refine ⟨29948759393246457845032451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19965839595497638563354967 29948759393246457845032451)
            ·
              refine ⟨44923139089869686767548677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29948759393246457845032451 44923139089869686767548677)
              ·
                refine ⟨8423088579350566268915377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44923139089869686767548677 8423088579350566268915377)
                ·
                  refine ⟨6317316434512924701686533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8423088579350566268915377 6317316434512924701686533)
                  ·
                    refine ⟨1184496831471173381566225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6317316434512924701686533 1184496831471173381566225)
                    ·
                      rfl

theorem cell23_6920398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 4, 2, 4].length) (baseStart_6920398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6920398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6920398 prefixEnd_6920398 := by exact prefixLift 6920398
  have htrace : WordTrace (prefixWord ++ tailWord_6920398) baseStart_6920398 baseEnd_6920398 := by
    simpa [prefixWord, tailWord_6920398, baseEnd_6920398] using wordTrace_append hprefix tailTrace_6920398
  have hstable : (prefixWord ++ tailWord_6920398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6920398).length < 2 ^ (prefixWord ++ tailWord_6920398).sum := by decide
  have hdescent : baseEnd_6920398 < baseStart_6920398 := by decide
  rcases family_descends (prefixWord ++ tailWord_6920398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6920438 : List Nat := [5, 1, 1, 1, 1, 1, 4, 2, 1, 3, 3]
def baseStart_6920438 : Nat := 118140960795 + 6920438 * 2 ^ 59
def prefixEnd_6920438 : Nat := 4983230072969 + 3 ^ 40 * 6920438 * 2
def baseEnd_6920438 : Nat := 3553511033639699988198491

theorem tailTrace_6920438 : CollatzResearch.WordTrace tailWord_6920438 prefixEnd_6920438 3553511033639699988198491 := by
  unfold tailWord_6920438
  simp only [CollatzResearch.WordTrace]
  refine ⟨15775569381402657347394623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 168272740068295011705542645 15775569381402657347394623)
  ·
    refine ⟨23663354072103986021091935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15775569381402657347394623 23663354072103986021091935)
    ·
      refine ⟨35495031108155979031637903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23663354072103986021091935 35495031108155979031637903)
      ·
        refine ⟨53242546662233968547456855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35495031108155979031637903 53242546662233968547456855)
        ·
          refine ⟨79863819993350952821185283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53242546662233968547456855 79863819993350952821185283)
          ·
            refine ⟨119795729990026429231777925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79863819993350952821185283 119795729990026429231777925)
            ·
              refine ⟨22461699373129955480958361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119795729990026429231777925 22461699373129955480958361)
              ·
                refine ⟨16846274529847466610718771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22461699373129955480958361 16846274529847466610718771)
                ·
                  refine ⟨25269411794771199916078157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16846274529847466610718771 25269411794771199916078157)
                  ·
                    refine ⟨9476029423039199968529309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25269411794771199916078157 9476029423039199968529309)
                    ·
                      refine ⟨3553511033639699988198491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9476029423039199968529309 3553511033639699988198491)
                      ·
                        rfl

theorem cell23_6920438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 2, 1, 3, 3].length) (baseStart_6920438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6920438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6920438 prefixEnd_6920438 := by exact prefixLift 6920438
  have htrace : WordTrace (prefixWord ++ tailWord_6920438) baseStart_6920438 baseEnd_6920438 := by
    simpa [prefixWord, tailWord_6920438, baseEnd_6920438] using wordTrace_append hprefix tailTrace_6920438
  have hstable : (prefixWord ++ tailWord_6920438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6920438).length < 2 ^ (prefixWord ++ tailWord_6920438).sum := by decide
  have hdescent : baseEnd_6920438 < baseStart_6920438 := by decide
  rcases family_descends (prefixWord ++ tailWord_6920438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6920471 : List Nat := [1, 1, 3, 4, 1, 2, 2, 1, 2, 6]
def baseStart_6920471 : Nat := 118140960795 + 6920471 * 2 ^ 59
def prefixEnd_6920471 : Nat := 4983230072969 + 3 ^ 40 * 6920471 * 2
def baseEnd_6920471 : Nat := 1184509326167099453028613

theorem tailTrace_6920471 : CollatzResearch.WordTrace tailWord_6920471 prefixEnd_6920471 1184509326167099453028613 := by
  unfold tailWord_6920471
  simp only [CollatzResearch.WordTrace]
  refine ⟨252410313711322964194265267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168273542474215309462843511 252410313711322964194265267)
  ·
    refine ⟨378615470566984446291397901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252410313711322964194265267 378615470566984446291397901)
    ·
      refine ⟨141980801462619167359274213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 378615470566984446291397901 141980801462619167359274213)
      ·
        refine ⟨26621400274241093879863915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141980801462619167359274213 26621400274241093879863915)
        ·
          refine ⟨39932100411361640819795873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26621400274241093879863915 39932100411361640819795873)
          ·
            refine ⟨29949075308521230614846905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39932100411361640819795873 29949075308521230614846905)
            ·
              refine ⟨22461806481390922961135179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29949075308521230614846905 22461806481390922961135179)
              ·
                refine ⟨33692709722086384441702769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22461806481390922961135179 33692709722086384441702769)
                ·
                  refine ⟨25269532291564788331277077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33692709722086384441702769 25269532291564788331277077)
                  ·
                    refine ⟨1184509326167099453028613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25269532291564788331277077 1184509326167099453028613)
                    ·
                      rfl

theorem cell23_6920471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 2, 6].length) (baseStart_6920471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6920471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6920471 prefixEnd_6920471 := by exact prefixLift 6920471
  have htrace : WordTrace (prefixWord ++ tailWord_6920471) baseStart_6920471 baseEnd_6920471 := by
    simpa [prefixWord, tailWord_6920471, baseEnd_6920471] using wordTrace_append hprefix tailTrace_6920471
  have hstable : (prefixWord ++ tailWord_6920471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6920471).length < 2 ^ (prefixWord ++ tailWord_6920471).sum := by decide
  have hdescent : baseEnd_6920471 < baseStart_6920471 := by decide
  rcases family_descends (prefixWord ++ tailWord_6920471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6920481 : List Nat := [1, 2, 3, 2, 1, 1, 2, 2, 2, 4, 3]
def baseStart_6920481 : Nat := 118140960795 + 6920481 * 2 ^ 59
def prefixEnd_6920481 : Nat := 4983230072969 + 3 ^ 40 * 6920481 * 2
def baseEnd_6920481 : Nat := 3553533113307843319960793

theorem tailTrace_6920481 : CollatzResearch.WordTrace tailWord_6920481 prefixEnd_6920481 3553533113307843319960793 := by
  unfold tailWord_6920481
  simp only [CollatzResearch.WordTrace]
  refine ⟨252410678441286735902129297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168273785627524490601419531 252410678441286735902129297)
  ·
    refine ⟨189308008830965051926596973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252410678441286735902129297 189308008830965051926596973)
    ·
      refine ⟨70990503311611894472473865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189308008830965051926596973 70990503311611894472473865)
      ·
        refine ⟨53242877483708920854355399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70990503311611894472473865 53242877483708920854355399)
        ·
          refine ⟨79864316225563381281533099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53242877483708920854355399 79864316225563381281533099)
          ·
            refine ⟨119796474338345071922299649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79864316225563381281533099 119796474338345071922299649)
            ·
              refine ⟨89847355753758803941724737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119796474338345071922299649 89847355753758803941724737)
              ·
                refine ⟨67385516815319102956293553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89847355753758803941724737 67385516815319102956293553)
                ·
                  refine ⟨50539137611489327217220165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67385516815319102956293553 50539137611489327217220165)
                  ·
                    refine ⟨9476088302154248853228781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50539137611489327217220165 9476088302154248853228781)
                    ·
                      refine ⟨3553533113307843319960793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9476088302154248853228781 3553533113307843319960793)
                      ·
                        rfl

theorem cell23_6920481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 4, 3].length) (baseStart_6920481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6920481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6920481 prefixEnd_6920481 := by exact prefixLift 6920481
  have htrace : WordTrace (prefixWord ++ tailWord_6920481) baseStart_6920481 baseEnd_6920481 := by
    simpa [prefixWord, tailWord_6920481, baseEnd_6920481] using wordTrace_append hprefix tailTrace_6920481
  have hstable : (prefixWord ++ tailWord_6920481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6920481).length < 2 ^ (prefixWord ++ tailWord_6920481).sum := by decide
  have hdescent : baseEnd_6920481 < baseStart_6920481 := by decide
  rcases family_descends (prefixWord ++ tailWord_6920481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6920482 : List Nat := [3, 3, 1, 1, 3, 2, 2, 2, 1, 3, 2]
def baseStart_6920482 : Nat := 118140960795 + 6920482 * 2 ^ 59
def prefixEnd_6920482 : Nat := 4983230072969 + 3 ^ 40 * 6920482 * 2
def baseEnd_6920482 : Nat := 3553533626788497816048289

theorem tailTrace_6920482 : CollatzResearch.WordTrace tailWord_6920482 prefixEnd_6920482 3553533626788497816048289 := by
  unfold tailWord_6920482
  simp only [CollatzResearch.WordTrace]
  refine ⟨63102678728570778268228925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168273809942855408715277133 63102678728570778268228925)
  ·
    refine ⟨23663504523214041850585847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63102678728570778268228925 23663504523214041850585847)
    ·
      refine ⟨35495256784821062775878771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23663504523214041850585847 35495256784821062775878771)
      ·
        refine ⟨53242885177231594163818157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35495256784821062775878771 53242885177231594163818157)
        ·
          refine ⟨19966081941461847811431809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53242885177231594163818157 19966081941461847811431809)
          ·
            refine ⟨14974561456096385858573857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19966081941461847811431809 14974561456096385858573857)
            ·
              refine ⟨11230921092072289393930393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14974561456096385858573857 11230921092072289393930393)
              ·
                refine ⟨8423190819054217045447795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11230921092072289393930393 8423190819054217045447795)
                ·
                  refine ⟨12634786228581325568171693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8423190819054217045447795 12634786228581325568171693)
                  ·
                    refine ⟨4738044835717997088064385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12634786228581325568171693 4738044835717997088064385)
                    ·
                      refine ⟨3553533626788497816048289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4738044835717997088064385 3553533626788497816048289)
                      ·
                        rfl

theorem cell23_6920482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 2, 1, 3, 2].length) (baseStart_6920482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6920482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6920482 prefixEnd_6920482 := by exact prefixLift 6920482
  have htrace : WordTrace (prefixWord ++ tailWord_6920482) baseStart_6920482 baseEnd_6920482 := by
    simpa [prefixWord, tailWord_6920482, baseEnd_6920482] using wordTrace_append hprefix tailTrace_6920482
  have hstable : (prefixWord ++ tailWord_6920482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6920482).length < 2 ^ (prefixWord ++ tailWord_6920482).sum := by decide
  have hdescent : baseEnd_6920482 < baseStart_6920482 := by decide
  rcases family_descends (prefixWord ++ tailWord_6920482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6920498 : List Nat := [3, 2, 1, 1, 5, 1, 1, 1, 2, 1, 5]
def baseStart_6920498 : Nat := 118140960795 + 6920498 * 2 ^ 59
def prefixEnd_6920498 : Nat := 4983230072969 + 3 ^ 40 * 6920498 * 2
def baseEnd_6920498 : Nat := 3553541842478969753448215

theorem tailTrace_6920498 : CollatzResearch.WordTrace tailWord_6920498 prefixEnd_6920498 3553541842478969753448215 := by
  unfold tailWord_6920498
  simp only [CollatzResearch.WordTrace]
  refine ⟨63102824620556286951374537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168274198988150098536998765 63102824620556286951374537)
  ·
    refine ⟨47327118465417215213530903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63102824620556286951374537 47327118465417215213530903)
    ·
      refine ⟨70990677698125822820296355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47327118465417215213530903 70990677698125822820296355)
      ·
        refine ⟨106486016547188734230444533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70990677698125822820296355 106486016547188734230444533)
        ·
          refine ⟨9983064051298943834104175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 106486016547188734230444533 9983064051298943834104175)
          ·
            refine ⟨14974596076948415751156263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9983064051298943834104175 14974596076948415751156263)
            ·
              refine ⟨22461894115422623626734395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14974596076948415751156263 22461894115422623626734395)
              ·
                refine ⟨33692841173133935440101593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22461894115422623626734395 33692841173133935440101593)
                ·
                  refine ⟨25269630879850451580076195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33692841173133935440101593 25269630879850451580076195)
                  ·
                    refine ⟨37904446319775677370114293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25269630879850451580076195 37904446319775677370114293)
                    ·
                      refine ⟨3553541842478969753448215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37904446319775677370114293 3553541842478969753448215)
                      ·
                        rfl

theorem cell23_6920498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 2, 1, 5].length) (baseStart_6920498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6920498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6920498 prefixEnd_6920498 := by exact prefixLift 6920498
  have htrace : WordTrace (prefixWord ++ tailWord_6920498) baseStart_6920498 baseEnd_6920498 := by
    simpa [prefixWord, tailWord_6920498, baseEnd_6920498] using wordTrace_append hprefix tailTrace_6920498
  have hstable : (prefixWord ++ tailWord_6920498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6920498).length < 2 ^ (prefixWord ++ tailWord_6920498).sum := by decide
  have hdescent : baseEnd_6920498 < baseStart_6920498 := by decide
  rcases family_descends (prefixWord ++ tailWord_6920498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6920529 : List Nat := [1, 2, 2, 1, 4, 4, 2, 1, 2, 2, 2]
def baseStart_6920529 : Nat := 118140960795 + 6920529 * 2 ^ 59
def prefixEnd_6920529 : Nat := 4983230072969 + 3 ^ 40 * 6920529 * 2
def baseEnd_6920529 : Nat := 3553557760379259132160573

theorem tailTrace_6920529 : CollatzResearch.WordTrace tailWord_6920529 prefixEnd_6920529 3553557760379259132160573 := by
  unfold tailWord_6920529
  simp only [CollatzResearch.WordTrace]
  refine ⟨252412429145112840099876641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168274952763408560066584427 252412429145112840099876641)
  ·
    refine ⟨189309321858834630074907481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252412429145112840099876641 189309321858834630074907481)
    ·
      refine ⟨141981991394125972556180611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189309321858834630074907481 141981991394125972556180611)
      ·
        refine ⟨212972987091188958834270917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141981991394125972556180611 212972987091188958834270917)
        ·
          refine ⟨39932435079597929781425797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 212972987091188958834270917 39932435079597929781425797)
          ·
            refine ⟨7487331577424611834017337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39932435079597929781425797 7487331577424611834017337)
            ·
              refine ⟨5615498683068458875513003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7487331577424611834017337 5615498683068458875513003)
              ·
                refine ⟨8423248024602688313269505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5615498683068458875513003 8423248024602688313269505)
                ·
                  refine ⟨6317436018452016234952129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8423248024602688313269505 6317436018452016234952129)
                  ·
                    refine ⟨4738077013839012176214097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6317436018452016234952129 4738077013839012176214097)
                    ·
                      refine ⟨3553557760379259132160573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4738077013839012176214097 3553557760379259132160573)
                      ·
                        rfl

theorem cell23_6920529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 2, 1, 2, 2, 2].length) (baseStart_6920529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6920529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6920529 prefixEnd_6920529 := by exact prefixLift 6920529
  have htrace : WordTrace (prefixWord ++ tailWord_6920529) baseStart_6920529 baseEnd_6920529 := by
    simpa [prefixWord, tailWord_6920529, baseEnd_6920529] using wordTrace_append hprefix tailTrace_6920529
  have hstable : (prefixWord ++ tailWord_6920529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6920529).length < 2 ^ (prefixWord ++ tailWord_6920529).sum := by decide
  have hdescent : baseEnd_6920529 < baseStart_6920529 := by decide
  rcases family_descends (prefixWord ++ tailWord_6920529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6920548 : List Nat := [2, 3, 1, 1, 3, 1, 4, 1, 2, 5]
def baseStart_6920548 : Nat := 118140960795 + 6920548 * 2 ^ 59
def prefixEnd_6920548 : Nat := 4983230072969 + 3 ^ 40 * 6920548 * 2
def baseEnd_6920548 : Nat := 1184522505503898185940995

theorem tailTrace_6920548 : CollatzResearch.WordTrace tailWord_6920548 prefixEnd_6920548 1184522505503898185940995 := by
  unfold tailWord_6920548
  simp only [CollatzResearch.WordTrace]
  refine ⟨126206561066022003172409149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168275414754696004229878865 126206561066022003172409149)
  ·
    refine ⟨47327460399758251189653431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126206561066022003172409149 47327460399758251189653431)
    ·
      refine ⟨70991190599637376784480147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47327460399758251189653431 70991190599637376784480147)
      ·
        refine ⟨106486785899456065176720221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70991190599637376784480147 106486785899456065176720221)
        ·
          refine ⟨39932544712296024441270083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106486785899456065176720221 39932544712296024441270083)
          ·
            refine ⟨59898817068444036661905125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39932544712296024441270083 59898817068444036661905125)
            ·
              refine ⟨11231028200333256874107211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59898817068444036661905125 11231028200333256874107211)
              ·
                refine ⟨16846542300499885311160817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11231028200333256874107211 16846542300499885311160817)
                ·
                  refine ⟨12634906725374913983370613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16846542300499885311160817 12634906725374913983370613)
                  ·
                    refine ⟨1184522505503898185940995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12634906725374913983370613 1184522505503898185940995)
                    ·
                      rfl

theorem cell23_6920548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 1, 2, 5].length) (baseStart_6920548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6920548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6920548 prefixEnd_6920548 := by exact prefixLift 6920548
  have htrace : WordTrace (prefixWord ++ tailWord_6920548) baseStart_6920548 baseEnd_6920548 := by
    simpa [prefixWord, tailWord_6920548, baseEnd_6920548] using wordTrace_append hprefix tailTrace_6920548
  have hstable : (prefixWord ++ tailWord_6920548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6920548).length < 2 ^ (prefixWord ++ tailWord_6920548).sum := by decide
  have hdescent : baseEnd_6920548 < baseStart_6920548 := by decide
  rcases family_descends (prefixWord ++ tailWord_6920548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6920581 : List Nat := [1, 3, 1, 1, 3, 1, 1, 2, 2, 4, 4]
def baseStart_6920581 : Nat := 118140960795 + 6920581 * 2 ^ 59
def prefixEnd_6920581 : Nat := 4983230072969 + 3 ^ 40 * 6920581 * 2
def baseEnd_6920581 : Nat := 3553584461373292928710333

theorem tailTrace_6920581 : CollatzResearch.WordTrace tailWord_6920581 prefixEnd_6920581 3553584461373292928710333 := by
  unfold tailWord_6920581
  simp only [CollatzResearch.WordTrace]
  refine ⟨252414325740924452980769597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168276217160616301987179731 252414325740924452980769597)
  ·
    refine ⟨94655372152846669867788599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252414325740924452980769597 94655372152846669867788599)
    ·
      refine ⟨141983058229270004801682899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94655372152846669867788599 141983058229270004801682899)
      ·
        refine ⟨212974587343905007202524349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141983058229270004801682899 212974587343905007202524349)
        ·
          refine ⟨79865470253964377700946631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212974587343905007202524349 79865470253964377700946631)
          ·
            refine ⟨119798205380946566551419947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79865470253964377700946631 119798205380946566551419947)
            ·
              refine ⟨179697308071419849827129921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119798205380946566551419947 179697308071419849827129921)
              ·
                refine ⟨134772981053564887370347441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179697308071419849827129921 134772981053564887370347441)
                ·
                  refine ⟨101079735790173665527760581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134772981053564887370347441 101079735790173665527760581)
                  ·
                    refine ⟨18952450460657562286455109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 101079735790173665527760581 18952450460657562286455109)
                    ·
                      refine ⟨3553584461373292928710333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18952450460657562286455109 3553584461373292928710333)
                      ·
                        rfl

theorem cell23_6920581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 4, 4].length) (baseStart_6920581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6920581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6920581 prefixEnd_6920581 := by exact prefixLift 6920581
  have htrace : WordTrace (prefixWord ++ tailWord_6920581) baseStart_6920581 baseEnd_6920581 := by
    simpa [prefixWord, tailWord_6920581, baseEnd_6920581] using wordTrace_append hprefix tailTrace_6920581
  have hstable : (prefixWord ++ tailWord_6920581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6920581).length < 2 ^ (prefixWord ++ tailWord_6920581).sum := by decide
  have hdescent : baseEnd_6920581 < baseStart_6920581 := by decide
  rcases family_descends (prefixWord ++ tailWord_6920581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6920585 : List Nat := [1, 2, 1, 1, 6, 2, 1, 1, 2, 4, 2]
def baseStart_6920585 : Nat := 118140960795 + 6920585 * 2 ^ 59
def prefixEnd_6920585 : Nat := 4983230072969 + 3 ^ 40 * 6920585 * 2
def baseEnd_6920585 : Nat := 3553586515295910913060315

theorem tailTrace_6920585 : CollatzResearch.WordTrace tailWord_6920585 prefixEnd_6920585 3553586515295910913060315 := by
  unfold tailWord_6920585
  simp only [CollatzResearch.WordTrace]
  refine ⟨252414471632909961663915209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168276314421939974442610139 252414471632909961663915209)
  ·
    refine ⟨189310853724682471247936407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252414471632909961663915209 189310853724682471247936407)
    ·
      refine ⟨283966280587023706871904611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189310853724682471247936407 283966280587023706871904611)
      ·
        refine ⟨425949420880535560307856917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283966280587023706871904611 425949420880535560307856917)
        ·
          refine ⟨19966379103775104389430793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 425949420880535560307856917 19966379103775104389430793)
          ·
            refine ⟨14974784327831328292073095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19966379103775104389430793 14974784327831328292073095)
            ·
              refine ⟨22462176491746992438109643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14974784327831328292073095 22462176491746992438109643)
              ·
                refine ⟨33693264737620488657164465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22462176491746992438109643 33693264737620488657164465)
                ·
                  refine ⟨25269948553215366492873349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33693264737620488657164465 25269948553215366492873349)
                  ·
                    refine ⟨4738115353727881217413753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25269948553215366492873349 4738115353727881217413753)
                    ·
                      refine ⟨3553586515295910913060315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4738115353727881217413753 3553586515295910913060315)
                      ·
                        rfl

theorem cell23_6920585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 2, 4, 2].length) (baseStart_6920585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6920585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6920585 prefixEnd_6920585 := by exact prefixLift 6920585
  have htrace : WordTrace (prefixWord ++ tailWord_6920585) baseStart_6920585 baseEnd_6920585 := by
    simpa [prefixWord, tailWord_6920585, baseEnd_6920585] using wordTrace_append hprefix tailTrace_6920585
  have hstable : (prefixWord ++ tailWord_6920585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6920585).length < 2 ^ (prefixWord ++ tailWord_6920585).sum := by decide
  have hdescent : baseEnd_6920585 < baseStart_6920585 := by decide
  rcases family_descends (prefixWord ++ tailWord_6920585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6920605 : List Nat := [1, 4, 2, 1, 4, 1, 1, 1, 1, 4, 3]
def baseStart_6920605 : Nat := 118140960795 + 6920605 * 2 ^ 59
def prefixEnd_6920605 : Nat := 4983230072969 + 3 ^ 40 * 6920605 * 2
def baseEnd_6920605 : Nat := 3553596784909000834810223

theorem tailTrace_6920605 : CollatzResearch.WordTrace tailWord_6920605 prefixEnd_6920605 3553596784909000834810223 := by
  unfold tailWord_6920605
  simp only [CollatzResearch.WordTrace]
  refine ⟨252415201092837505079643269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168276800728558336719762179 252415201092837505079643269)
  ·
    refine ⟨47327850204907032202433113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 252415201092837505079643269 47327850204907032202433113)
    ·
      refine ⟨35495887653680274151824835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47327850204907032202433113 35495887653680274151824835)
      ·
        refine ⟨53243831480520411227737253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35495887653680274151824835 53243831480520411227737253)
        ·
          refine ⟨9983218402597577105200735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53243831480520411227737253 9983218402597577105200735)
          ·
            refine ⟨14974827603896365657801103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9983218402597577105200735 14974827603896365657801103)
            ·
              refine ⟨22462241405844548486701655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14974827603896365657801103 22462241405844548486701655)
              ·
                refine ⟨33693362108766822730052483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22462241405844548486701655 33693362108766822730052483)
                ·
                  refine ⟨50540043163150234095078725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33693362108766822730052483 50540043163150234095078725)
                  ·
                    refine ⟨9476258093090668892827261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50540043163150234095078725 9476258093090668892827261)
                    ·
                      refine ⟨3553596784909000834810223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9476258093090668892827261 3553596784909000834810223)
                      ·
                        rfl

theorem cell23_6920605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 4, 3].length) (baseStart_6920605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6920605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6920605 prefixEnd_6920605 := by exact prefixLift 6920605
  have htrace : WordTrace (prefixWord ++ tailWord_6920605) baseStart_6920605 baseEnd_6920605 := by
    simpa [prefixWord, tailWord_6920605, baseEnd_6920605] using wordTrace_append hprefix tailTrace_6920605
  have hstable : (prefixWord ++ tailWord_6920605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6920605).length < 2 ^ (prefixWord ++ tailWord_6920605).sum := by decide
  have hdescent : baseEnd_6920605 < baseStart_6920605 := by decide
  rcases family_descends (prefixWord ++ tailWord_6920605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6920625 : List Nat := [1, 2, 2, 4, 1, 4, 1, 2, 6]
def baseStart_6920625 : Nat := 118140960795 + 6920625 * 2 ^ 59
def prefixEnd_6920625 : Nat := 4983230072969 + 3 ^ 40 * 6920625 * 2
def baseEnd_6920625 : Nat := 394845228280232306284459

theorem tailTrace_6920625 : CollatzResearch.WordTrace tailWord_6920625 prefixEnd_6920625 394845228280232306284459 := by
  unfold tailWord_6920625
  simp only [CollatzResearch.WordTrace]
  refine ⟨252415930552765048495371329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168277287035176698996914219 252415930552765048495371329)
  ·
    refine ⟨189311947914573786371528497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252415930552765048495371329 189311947914573786371528497)
    ·
      refine ⟨141983960935930339778646373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189311947914573786371528497 141983960935930339778646373)
      ·
        refine ⟨26621992675486938708496195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141983960935930339778646373 26621992675486938708496195)
        ·
          refine ⟨39932989013230408062744293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26621992675486938708496195 39932989013230408062744293)
          ·
            refine ⟨7487435439980701511764555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39932989013230408062744293 7487435439980701511764555)
            ·
              refine ⟨11231153159971052267646833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7487435439980701511764555 11231153159971052267646833)
              ·
                refine ⟨8423364869978289200735125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11231153159971052267646833 8423364869978289200735125)
                ·
                  refine ⟨394845228280232306284459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8423364869978289200735125 394845228280232306284459)
                  ·
                    rfl

theorem cell23_6920625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 2, 6].length) (baseStart_6920625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6920625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6920625 prefixEnd_6920625 := by exact prefixLift 6920625
  have htrace : WordTrace (prefixWord ++ tailWord_6920625) baseStart_6920625 baseEnd_6920625 := by
    simpa [prefixWord, tailWord_6920625, baseEnd_6920625] using wordTrace_append hprefix tailTrace_6920625
  have hstable : (prefixWord ++ tailWord_6920625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6920625).length < 2 ^ (prefixWord ++ tailWord_6920625).sum := by decide
  have hdescent : baseEnd_6920625 < baseStart_6920625 := by decide
  rcases family_descends (prefixWord ++ tailWord_6920625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6920638 : List Nat := [4, 2, 1, 1, 1, 1, 2, 1, 5, 5]
def baseStart_6920638 : Nat := 118140960795 + 6920638 * 2 ^ 59
def prefixEnd_6920638 : Nat := 4983230072969 + 3 ^ 40 * 6920638 * 2
def baseEnd_6920638 : Nat := 1184537909923533068565857

theorem tailTrace_6920638 : CollatzResearch.WordTrace tailWord_6920638 prefixEnd_6920638 1184537909923533068565857 := by
  unfold tailWord_6920638
  simp only [CollatzResearch.WordTrace]
  refine ⟨31552050587714743964449321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168277603134478634477063045 31552050587714743964449321)
  ·
    refine ⟨23664037940786057973336991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31552050587714743964449321 23664037940786057973336991)
    ·
      refine ⟨35496056911179086960005487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23664037940786057973336991 35496056911179086960005487)
      ·
        refine ⟨53244085366768630440008231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35496056911179086960005487 53244085366768630440008231)
        ·
          refine ⟨79866128050152945660012347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53244085366768630440008231 79866128050152945660012347)
          ·
            refine ⟨119799192075229418490018521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79866128050152945660012347 119799192075229418490018521)
            ·
              refine ⟨89849394056422063867513891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119799192075229418490018521 89849394056422063867513891)
              ·
                refine ⟨134774091084633095801270837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89849394056422063867513891 134774091084633095801270837)
                ·
                  refine ⟨12635071039184352731369141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 134774091084633095801270837 12635071039184352731369141)
                  ·
                    refine ⟨1184537909923533068565857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12635071039184352731369141 1184537909923533068565857)
                    ·
                      rfl

theorem cell23_6920638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_6920638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6920638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6920638 prefixEnd_6920638 := by exact prefixLift 6920638
  have htrace : WordTrace (prefixWord ++ tailWord_6920638) baseStart_6920638 baseEnd_6920638 := by
    simpa [prefixWord, tailWord_6920638, baseEnd_6920638] using wordTrace_append hprefix tailTrace_6920638
  have hstable : (prefixWord ++ tailWord_6920638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6920638).length < 2 ^ (prefixWord ++ tailWord_6920638).sum := by decide
  have hdescent : baseEnd_6920638 < baseStart_6920638 := by decide
  rcases family_descends (prefixWord ++ tailWord_6920638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6920662 : List Nat := [5, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2]
def baseStart_6920662 : Nat := 118140960795 + 6920662 * 2 ^ 59
def prefixEnd_6920662 : Nat := 4983230072969 + 3 ^ 40 * 6920662 * 2
def baseEnd_6920662 : Nat := 3553626053306307111797461

theorem tailTrace_6920662 : CollatzResearch.WordTrace tailWord_6920662 prefixEnd_6920662 3553626053306307111797461 := by
  unfold tailWord_6920662
  simp only [CollatzResearch.WordTrace]
  refine ⟨15776080003351937738404265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 168278186702420669209645493 15776080003351937738404265)
  ·
    refine ⟨11832060002513953303803199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15776080003351937738404265 11832060002513953303803199)
    ·
      refine ⟨17748090003770929955704799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11832060002513953303803199 17748090003770929955704799)
      ·
        refine ⟨26622135005656394933557199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17748090003770929955704799 26622135005656394933557199)
        ·
          refine ⟨39933202508484592400335799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26622135005656394933557199 39933202508484592400335799)
          ·
            refine ⟨59899803762726888600503699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39933202508484592400335799 59899803762726888600503699)
            ·
              refine ⟨89849705644090332900755549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59899803762726888600503699 89849705644090332900755549)
              ·
                refine ⟨33693639616533874837783331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89849705644090332900755549 33693639616533874837783331)
                ·
                  refine ⟨50540459424800812256674997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33693639616533874837783331 50540459424800812256674997)
                  ·
                    refine ⟨4738168071075076149063281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50540459424800812256674997 4738168071075076149063281)
                    ·
                      refine ⟨3553626053306307111797461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4738168071075076149063281 3553626053306307111797461)
                      ·
                        rfl

theorem cell23_6920662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2].length) (baseStart_6920662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6920662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6920662 prefixEnd_6920662 := by exact prefixLift 6920662
  have htrace : WordTrace (prefixWord ++ tailWord_6920662) baseStart_6920662 baseEnd_6920662 := by
    simpa [prefixWord, tailWord_6920662, baseEnd_6920662] using wordTrace_append hprefix tailTrace_6920662
  have hstable : (prefixWord ++ tailWord_6920662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6920662).length < 2 ^ (prefixWord ++ tailWord_6920662).sum := by decide
  have hdescent : baseEnd_6920662 < baseStart_6920662 := by decide
  rcases family_descends (prefixWord ++ tailWord_6920662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6920686 : List Nat := [4, 1, 2, 1, 2, 3, 3, 2, 1, 1, 3]
def baseStart_6920686 : Nat := 118140960795 + 6920686 * 2 ^ 59
def prefixEnd_6920686 : Nat := 4983230072969 + 3 ^ 40 * 6920686 * 2
def baseEnd_6920686 : Nat := 3553638376842015017897351

theorem tailTrace_6920686 : CollatzResearch.WordTrace tailWord_6920686 prefixEnd_6920686 3553638376842015017897351 := by
  unfold tailWord_6920686
  simp only [CollatzResearch.WordTrace]
  refine ⟨31552269425693006989167739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168278770270362703942227941 31552269425693006989167739)
  ·
    refine ⟨47328404138539510483751609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31552269425693006989167739 47328404138539510483751609)
    ·
      refine ⟨35496303103904632862813707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47328404138539510483751609 35496303103904632862813707)
      ·
        refine ⟨53244454655856949294220561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35496303103904632862813707 53244454655856949294220561)
        ·
          refine ⟨39933340991892711970665421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53244454655856949294220561 39933340991892711970665421)
          ·
            refine ⟨14975002871959766988999533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39933340991892711970665421 14975002871959766988999533)
            ·
              refine ⟨5615626076984912620874825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14975002871959766988999533 5615626076984912620874825)
              ·
                refine ⟨4211719557738684465656119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5615626076984912620874825 4211719557738684465656119)
                ·
                  refine ⟨6317579336608026698484179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4211719557738684465656119 6317579336608026698484179)
                  ·
                    refine ⟨9476369004912040047726269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6317579336608026698484179 9476369004912040047726269)
                    ·
                      refine ⟨3553638376842015017897351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9476369004912040047726269 3553638376842015017897351)
                      ·
                        rfl

theorem cell23_6920686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 3, 2, 1, 1, 3].length) (baseStart_6920686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6920686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6920686 prefixEnd_6920686 := by exact prefixLift 6920686
  have htrace : WordTrace (prefixWord ++ tailWord_6920686) baseStart_6920686 baseEnd_6920686 := by
    simpa [prefixWord, tailWord_6920686, baseEnd_6920686] using wordTrace_append hprefix tailTrace_6920686
  have hstable : (prefixWord ++ tailWord_6920686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6920686).length < 2 ^ (prefixWord ++ tailWord_6920686).sum := by decide
  have hdescent : baseEnd_6920686 < baseStart_6920686 := by decide
  rcases family_descends (prefixWord ++ tailWord_6920686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6920706 : List Nat := [3, 4, 1, 2, 3, 1, 1, 2, 1, 5]
def baseStart_6920706 : Nat := 118140960795 + 6920706 * 2 ^ 59
def prefixEnd_6920706 : Nat := 4983230072969 + 3 ^ 40 * 6920706 * 2
def baseEnd_6920706 : Nat := 1184549548818368313215753

theorem tailTrace_6920706 : CollatzResearch.WordTrace tailWord_6920706 prefixEnd_6920706 1184549548818368313215753 := by
  unfold tailWord_6920706
  simp only [CollatzResearch.WordTrace]
  refine ⟨63104721216367899832267493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168279256576981066219379981 63104721216367899832267493)
  ·
    refine ⟨11832135228068981218550155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63104721216367899832267493 11832135228068981218550155)
    ·
      refine ⟨17748202842103471827825233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11832135228068981218550155 17748202842103471827825233)
      ·
        refine ⟨13311152131577603870868925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17748202842103471827825233 13311152131577603870868925)
        ·
          refine ⟨4991682049341601451575847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13311152131577603870868925 4991682049341601451575847)
          ·
            refine ⟨7487523074012402177363771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4991682049341601451575847 7487523074012402177363771)
            ·
              refine ⟨11231284611018603266045657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7487523074012402177363771 11231284611018603266045657)
              ·
                refine ⟨8423463458263952449534243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11231284611018603266045657 8423463458263952449534243)
                ·
                  refine ⟨12635195187395928674301365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8423463458263952449534243 12635195187395928674301365)
                  ·
                    refine ⟨1184549548818368313215753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12635195187395928674301365 1184549548818368313215753)
                    ·
                      rfl

theorem cell23_6920706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_6920706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6920706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6920706 prefixEnd_6920706 := by exact prefixLift 6920706
  have htrace : WordTrace (prefixWord ++ tailWord_6920706) baseStart_6920706 baseEnd_6920706 := by
    simpa [prefixWord, tailWord_6920706, baseEnd_6920706] using wordTrace_append hprefix tailTrace_6920706
  have hstable : (prefixWord ++ tailWord_6920706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6920706).length < 2 ^ (prefixWord ++ tailWord_6920706).sum := by decide
  have hdescent : baseEnd_6920706 < baseStart_6920706 := by decide
  rcases family_descends (prefixWord ++ tailWord_6920706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6920725 : List Nat := [1, 3, 2, 1, 3, 1, 3, 2, 1, 3, 3]
def baseStart_6920725 : Nat := 118140960795 + 6920725 * 2 ^ 59
def prefixEnd_6920725 : Nat := 4983230072969 + 3 ^ 40 * 6920725 * 2
def baseEnd_6920725 : Nat := 3553658402587540365309671

theorem tailTrace_6920725 : CollatzResearch.WordTrace tailWord_6920725 prefixEnd_6920725 3553658402587540365309671 := by
  unfold tailWord_6920725
  simp only [CollatzResearch.WordTrace]
  refine ⟨252419577852402765574011629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168279718568268510382674419 252419577852402765574011629)
  ·
    refine ⟨94657341694651037090254361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252419577852402765574011629 94657341694651037090254361)
    ·
      refine ⟨70993006270988277817690771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94657341694651037090254361 70993006270988277817690771)
      ·
        refine ⟨106489509406482416726536157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70993006270988277817690771 106489509406482416726536157)
        ·
          refine ⟨39933566027430906272451059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106489509406482416726536157 39933566027430906272451059)
          ·
            refine ⟨59900349041146359408676589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39933566027430906272451059 59900349041146359408676589)
            ·
              refine ⟨22462630890429884778253721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59900349041146359408676589 22462630890429884778253721)
              ·
                refine ⟨16846973167822413583690291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22462630890429884778253721 16846973167822413583690291)
                ·
                  refine ⟨25270459751733620375535437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16846973167822413583690291 25270459751733620375535437)
                  ·
                    refine ⟨9476422406900107640825789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25270459751733620375535437 9476422406900107640825789)
                    ·
                      refine ⟨3553658402587540365309671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9476422406900107640825789 3553658402587540365309671)
                      ·
                        rfl

theorem cell23_6920725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 2, 1, 3, 3].length) (baseStart_6920725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6920725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6920725 prefixEnd_6920725 := by exact prefixLift 6920725
  have htrace : WordTrace (prefixWord ++ tailWord_6920725) baseStart_6920725 baseEnd_6920725 := by
    simpa [prefixWord, tailWord_6920725, baseEnd_6920725] using wordTrace_append hprefix tailTrace_6920725
  have hstable : (prefixWord ++ tailWord_6920725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6920725).length < 2 ^ (prefixWord ++ tailWord_6920725).sum := by decide
  have hdescent : baseEnd_6920725 < baseStart_6920725 := by decide
  rcases family_descends (prefixWord ++ tailWord_6920725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6920768 : List Nat := [2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 5]
def baseStart_6920768 : Nat := 118140960795 + 6920768 * 2 ^ 59
def prefixEnd_6920768 : Nat := 4983230072969 + 3 ^ 40 * 6920768 * 2
def baseEnd_6920768 : Nat := 3553680482255683697071973

theorem tailTrace_6920768 : CollatzResearch.WordTrace tailWord_6920768 prefixEnd_6920768 3553680482255683697071973 := by
  unfold tailWord_6920768
  simp only [CollatzResearch.WordTrace]
  refine ⟨126210573095623491958913479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168280764127497989278551305 126210573095623491958913479)
  ·
    refine ⟨189315859643435237938370219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126210573095623491958913479 189315859643435237938370219)
    ·
      refine ⟨283973789465152856907555329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189315859643435237938370219 283973789465152856907555329)
      ·
        refine ⟨212980342098864642680666497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283973789465152856907555329 212980342098864642680666497)
        ·
          refine ⟨159735256574148482010499873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212980342098864642680666497 159735256574148482010499873)
          ·
            refine ⟨119801442430611361507874905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159735256574148482010499873 119801442430611361507874905)
            ·
              refine ⟨89851081822958521130906179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119801442430611361507874905 89851081822958521130906179)
              ·
                refine ⟨134776622734437781696359269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89851081822958521130906179 134776622734437781696359269)
                ·
                  refine ⟨25270616762707084068067363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 134776622734437781696359269 25270616762707084068067363)
                  ·
                    refine ⟨37905925144060626102101045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25270616762707084068067363 37905925144060626102101045)
                    ·
                      refine ⟨3553680482255683697071973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37905925144060626102101045 3553680482255683697071973)
                      ·
                        rfl

theorem cell23_6920768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 5].length) (baseStart_6920768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6920768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6920768 prefixEnd_6920768 := by exact prefixLift 6920768
  have htrace : WordTrace (prefixWord ++ tailWord_6920768) baseStart_6920768 baseEnd_6920768 := by
    simpa [prefixWord, tailWord_6920768, baseEnd_6920768] using wordTrace_append hprefix tailTrace_6920768
  have hstable : (prefixWord ++ tailWord_6920768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6920768).length < 2 ^ (prefixWord ++ tailWord_6920768).sum := by decide
  have hdescent : baseEnd_6920768 < baseStart_6920768 := by decide
  rcases family_descends (prefixWord ++ tailWord_6920768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6920782 : List Nat := [4, 1, 1, 1, 1, 2, 4, 2, 1, 4, 2]
def baseStart_6920782 : Nat := 118140960795 + 6920782 * 2 ^ 59
def prefixEnd_6920782 : Nat := 4983230072969 + 3 ^ 40 * 6920782 * 2
def baseEnd_6920782 : Nat := 3553687670984846642296909

theorem tailTrace_6920782 : CollatzResearch.WordTrace tailWord_6920782 prefixEnd_6920782 3553687670984846642296909 := by
  unfold tailWord_6920782
  simp only [CollatzResearch.WordTrace]
  refine ⟨31552707101649533038604575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168281104542130842872557733 31552707101649533038604575)
  ·
    refine ⟨47329060652474299557906863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31552707101649533038604575 47329060652474299557906863)
    ·
      refine ⟨70993590978711449336860295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47329060652474299557906863 70993590978711449336860295)
      ·
        refine ⟨106490386468067174005290443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70993590978711449336860295 106490386468067174005290443)
        ·
          refine ⟨159735579702100761007935665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106490386468067174005290443 159735579702100761007935665)
          ·
            refine ⟨119801684776575570755951749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159735579702100761007935665 119801684776575570755951749)
            ·
              refine ⟨22462815895607919516740953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119801684776575570755951749 22462815895607919516740953)
              ·
                refine ⟨16847111921705939637555715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22462815895607919516740953 16847111921705939637555715)
                ·
                  refine ⟨25270667882558909456333573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16847111921705939637555715 25270667882558909456333573)
                  ·
                    refine ⟨4738250227979795523062545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25270667882558909456333573 4738250227979795523062545)
                    ·
                      refine ⟨3553687670984846642296909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4738250227979795523062545 3553687670984846642296909)
                      ·
                        rfl

theorem cell23_6920782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 2, 1, 4, 2].length) (baseStart_6920782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6920782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6920782 prefixEnd_6920782 := by exact prefixLift 6920782
  have htrace : WordTrace (prefixWord ++ tailWord_6920782) baseStart_6920782 baseEnd_6920782 := by
    simpa [prefixWord, tailWord_6920782, baseEnd_6920782] using wordTrace_append hprefix tailTrace_6920782
  have hstable : (prefixWord ++ tailWord_6920782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6920782).length < 2 ^ (prefixWord ++ tailWord_6920782).sum := by decide
  have hdescent : baseEnd_6920782 < baseStart_6920782 := by decide
  rcases family_descends (prefixWord ++ tailWord_6920782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6920815 : List Nat := [1, 1, 2, 1, 3, 2, 4, 1, 2, 3, 3]
def baseStart_6920815 : Nat := 118140960795 + 6920815 * 2 ^ 59
def prefixEnd_6920815 : Nat := 4983230072969 + 3 ^ 40 * 6920815 * 2
def baseEnd_6920815 : Nat := 3553704615846445013184257

theorem tailTrace_6920815 : CollatzResearch.WordTrace tailWord_6920815 prefixEnd_6920815 3553704615846445013184257 := by
  unfold tailWord_6920815
  simp only [CollatzResearch.WordTrace]
  refine ⟨252422860422076710944787899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168281906948051140629858599 252422860422076710944787899)
  ·
    refine ⟨378634290633115066417181849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252422860422076710944787899 378634290633115066417181849)
    ·
      refine ⟨283975717974836299812886387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 378634290633115066417181849 283975717974836299812886387)
      ·
        refine ⟨425963576962254449719329581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283975717974836299812886387 425963576962254449719329581)
        ·
          refine ⟨159736341360845418644748593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 425963576962254449719329581 159736341360845418644748593)
          ·
            refine ⟨119802256020634063983561445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159736341360845418644748593 119802256020634063983561445)
            ·
              refine ⟨22462923003868886996917771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119802256020634063983561445 22462923003868886996917771)
              ·
                refine ⟨33694384505803330495376657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22462923003868886996917771 33694384505803330495376657)
                ·
                  refine ⟨25270788379352497871532493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33694384505803330495376657 25270788379352497871532493)
                  ·
                    refine ⟨9476545642257186701824685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25270788379352497871532493 9476545642257186701824685)
                    ·
                      refine ⟨3553704615846445013184257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9476545642257186701824685 3553704615846445013184257)
                      ·
                        rfl

theorem cell23_6920815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 2, 3, 3].length) (baseStart_6920815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6920815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6920815 prefixEnd_6920815 := by exact prefixLift 6920815
  have htrace : WordTrace (prefixWord ++ tailWord_6920815) baseStart_6920815 baseEnd_6920815 := by
    simpa [prefixWord, tailWord_6920815, baseEnd_6920815] using wordTrace_append hprefix tailTrace_6920815
  have hstable : (prefixWord ++ tailWord_6920815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6920815).length < 2 ^ (prefixWord ++ tailWord_6920815).sum := by decide
  have hdescent : baseEnd_6920815 < baseStart_6920815 := by decide
  rcases family_descends (prefixWord ++ tailWord_6920815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6920816 : List Nat := [2, 1, 1, 1, 8, 1, 1, 1, 1, 4, 2]
def baseStart_6920816 : Nat := 118140960795 + 6920816 * 2 ^ 59
def prefixEnd_6920816 : Nat := 4983230072969 + 3 ^ 40 * 6920816 * 2
def baseEnd_6920816 : Nat := 3553705129327099509271753

theorem tailTrace_6920816 : CollatzResearch.WordTrace tailWord_6920816 prefixEnd_6920816 3553705129327099509271753 := by
  unfold tailWord_6920816
  simp only [CollatzResearch.WordTrace]
  refine ⟨126211448447536544057787151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168281931263382058743716201 126211448447536544057787151)
  ·
    refine ⟨189317172671304816086680727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126211448447536544057787151 189317172671304816086680727)
    ·
      refine ⟨283975759006957224130021091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189317172671304816086680727 283975759006957224130021091)
      ·
        refine ⟨425963638510435836195031637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283975759006957224130021091 425963638510435836195031637)
        ·
          refine ⟨4991761388794169955410527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 425963638510435836195031637 4991761388794169955410527)
          ·
            refine ⟨7487642083191254933115791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4991761388794169955410527 7487642083191254933115791)
            ·
              refine ⟨11231463124786882399673687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7487642083191254933115791 11231463124786882399673687)
              ·
                refine ⟨16847194687180323599510531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11231463124786882399673687 16847194687180323599510531)
                ·
                  refine ⟨25270792030770485399265797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16847194687180323599510531 25270792030770485399265797)
                  ·
                    refine ⟨4738273505769466012362337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25270792030770485399265797 4738273505769466012362337)
                    ·
                      refine ⟨3553705129327099509271753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4738273505769466012362337 3553705129327099509271753)
                      ·
                        rfl

theorem cell23_6920816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 1, 1, 4, 2].length) (baseStart_6920816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6920816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6920816 prefixEnd_6920816 := by exact prefixLift 6920816
  have htrace : WordTrace (prefixWord ++ tailWord_6920816) baseStart_6920816 baseEnd_6920816 := by
    simpa [prefixWord, tailWord_6920816, baseEnd_6920816] using wordTrace_append hprefix tailTrace_6920816
  have hstable : (prefixWord ++ tailWord_6920816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6920816).length < 2 ^ (prefixWord ++ tailWord_6920816).sum := by decide
  have hdescent : baseEnd_6920816 < baseStart_6920816 := by decide
  rcases family_descends (prefixWord ++ tailWord_6920816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6920852 : List Nat := [2, 4, 2, 2, 1, 1, 1, 1, 4, 5]
def baseStart_6920852 : Nat := 118140960795 + 6920852 * 2 ^ 59
def prefixEnd_6920852 : Nat := 4983230072969 + 3 ^ 40 * 6920852 * 2
def baseEnd_6920852 : Nat := 1184574538210220456140529

theorem tailTrace_6920852 : CollatzResearch.WordTrace tailWord_6920852 prefixEnd_6920852 1184574538210220456140529 := by
  unfold tailWord_6920852
  simp only [CollatzResearch.WordTrace]
  refine ⟨126212104961471333131942405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168282806615295110842589873 126212104961471333131942405)
  ·
    refine ⟨23664769680275874962239201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126212104961471333131942405 23664769680275874962239201)
    ·
      refine ⟨17748577260206906221679401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23664769680275874962239201 17748577260206906221679401)
      ·
        refine ⟨13311432945155179666259551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17748577260206906221679401 13311432945155179666259551)
        ·
          refine ⟨19967149417732769499389327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13311432945155179666259551 19967149417732769499389327)
          ·
            refine ⟨29950724126599154249083991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19967149417732769499389327 29950724126599154249083991)
            ·
              refine ⟨44926086189898731373625987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29950724126599154249083991 44926086189898731373625987)
              ·
                refine ⟨67389129284848097060438981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44926086189898731373625987 67389129284848097060438981)
                ·
                  refine ⟨12635461740909018198832309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67389129284848097060438981 12635461740909018198832309)
                  ·
                    refine ⟨1184574538210220456140529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12635461740909018198832309 1184574538210220456140529)
                    ·
                      rfl

theorem cell23_6920852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_6920852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6920852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6920852 prefixEnd_6920852 := by exact prefixLift 6920852
  have htrace : WordTrace (prefixWord ++ tailWord_6920852) baseStart_6920852 baseEnd_6920852 := by
    simpa [prefixWord, tailWord_6920852, baseEnd_6920852] using wordTrace_append hprefix tailTrace_6920852
  have hstable : (prefixWord ++ tailWord_6920852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6920852).length < 2 ^ (prefixWord ++ tailWord_6920852).sum := by decide
  have hdescent : baseEnd_6920852 < baseStart_6920852 := by decide
  rcases family_descends (prefixWord ++ tailWord_6920852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6920862 : List Nat := [4, 3, 1, 1, 1, 1, 3, 1, 1, 2, 5]
def baseStart_6920862 : Nat := 118140960795 + 6920862 * 2 ^ 59
def prefixEnd_6920862 : Nat := 4983230072969 + 3 ^ 40 * 6920862 * 2
def baseEnd_6920862 : Nat := 3553728749437206329296541

theorem tailTrace_6920862 : CollatzResearch.WordTrace tailWord_6920862 prefixEnd_6920862 3553728749437206329296541 := by
  unfold tailWord_6920862
  simp only [CollatzResearch.WordTrace]
  refine ⟨31553071831613304746468605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168283049768604291981165893 31553071831613304746468605)
  ·
    refine ⟨11832401936854989279925727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31553071831613304746468605 11832401936854989279925727)
    ·
      refine ⟨17748602905282483919888591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11832401936854989279925727 17748602905282483919888591)
      ·
        refine ⟨26622904357923725879832887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17748602905282483919888591 26622904357923725879832887)
        ·
          refine ⟨39934356536885588819749331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26622904357923725879832887 39934356536885588819749331)
          ·
            refine ⟨59901534805328383229623997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39934356536885588819749331 59901534805328383229623997)
            ·
              refine ⟨22463075551998143711108999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59901534805328383229623997 22463075551998143711108999)
              ·
                refine ⟨33694613327997215566663499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22463075551998143711108999 33694613327997215566663499)
                ·
                  refine ⟨50541919991995823349995249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33694613327997215566663499 50541919991995823349995249)
                  ·
                    refine ⟨37906439993996867512496437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50541919991995823349995249 37906439993996867512496437)
                    ·
                      refine ⟨3553728749437206329296541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37906439993996867512496437 3553728749437206329296541)
                      ·
                        rfl

theorem cell23_6920862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_6920862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6920862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6920862 prefixEnd_6920862 := by exact prefixLift 6920862
  have htrace : WordTrace (prefixWord ++ tailWord_6920862) baseStart_6920862 baseEnd_6920862 := by
    simpa [prefixWord, tailWord_6920862, baseEnd_6920862] using wordTrace_append hprefix tailTrace_6920862
  have hstable : (prefixWord ++ tailWord_6920862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6920862).length < 2 ^ (prefixWord ++ tailWord_6920862).sum := by decide
  have hdescent : baseEnd_6920862 < baseStart_6920862 := by decide
  rcases family_descends (prefixWord ++ tailWord_6920862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6920886 : List Nat := [5, 1, 3, 1, 2, 1, 2, 1, 2, 5]
def baseStart_6920886 : Nat := 118140960795 + 6920886 * 2 ^ 59
def prefixEnd_6920886 : Nat := 4983230072969 + 3 ^ 40 * 6920886 * 2
def baseEnd_6920886 : Nat := 1184580357657638078465477

theorem tailTrace_6920886 : CollatzResearch.WordTrace tailWord_6920886 prefixEnd_6920886 1184580357657638078465477 := by
  unfold tailWord_6920886
  simp only [CollatzResearch.WordTrace]
  refine ⟨15776590625301218129413907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 168283633336546326713748341 15776590625301218129413907)
  ·
    refine ⟨23664885937951827194120861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15776590625301218129413907 23664885937951827194120861)
    ·
      refine ⟨8874332226731935197795323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23664885937951827194120861 8874332226731935197795323)
      ·
        refine ⟨13311498340097902796692985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8874332226731935197795323 13311498340097902796692985)
        ·
          refine ⟨9983623755073427097519739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13311498340097902796692985 9983623755073427097519739)
          ·
            refine ⟨14975435632610140646279609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9983623755073427097519739 14975435632610140646279609)
            ·
              refine ⟨11231576724457605484709707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14975435632610140646279609 11231576724457605484709707)
              ·
                refine ⟨16847365086686408227064561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11231576724457605484709707 16847365086686408227064561)
                ·
                  refine ⟨12635523815014806170298421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16847365086686408227064561 12635523815014806170298421)
                  ·
                    refine ⟨1184580357657638078465477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12635523815014806170298421 1184580357657638078465477)
                    ·
                      rfl

theorem cell23_6920886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_6920886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6920886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6920886 prefixEnd_6920886 := by exact prefixLift 6920886
  have htrace : WordTrace (prefixWord ++ tailWord_6920886) baseStart_6920886 baseEnd_6920886 := by
    simpa [prefixWord, tailWord_6920886, baseEnd_6920886] using wordTrace_append hprefix tailTrace_6920886
  have hstable : (prefixWord ++ tailWord_6920886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6920886).length < 2 ^ (prefixWord ++ tailWord_6920886).sum := by decide
  have hdescent : baseEnd_6920886 < baseStart_6920886 := by decide
  rcases family_descends (prefixWord ++ tailWord_6920886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6920942 : List Nat := [4, 1, 2, 1, 1, 3, 2, 1, 3, 5]
def baseStart_6920942 : Nat := 118140960795 + 6920942 * 2 ^ 59
def prefixEnd_6920942 : Nat := 4983230072969 + 3 ^ 40 * 6920942 * 2
def baseEnd_6920942 : Nat := 1184589942629855338765391

theorem tailTrace_6920942 : CollatzResearch.WordTrace tailWord_6920942 prefixEnd_6920942 1184589942629855338765391 := by
  unfold tailWord_6920942
  simp only [CollatzResearch.WordTrace]
  refine ⟨31553436561577076454332635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168284994995077741089774053 31553436561577076454332635)
  ·
    refine ⟨47330154842365614681498953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31553436561577076454332635 47330154842365614681498953)
    ·
      refine ⟨35497616131774211011124215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47330154842365614681498953 35497616131774211011124215)
      ·
        refine ⟨53246424197661316516686323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35497616131774211011124215 53246424197661316516686323)
        ·
          refine ⟨79869636296491974775029485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53246424197661316516686323 79869636296491974775029485)
          ·
            refine ⟨29951113611184490540636057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79869636296491974775029485 29951113611184490540636057)
            ·
              refine ⟨22463335208388367905477043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29951113611184490540636057 22463335208388367905477043)
              ·
                refine ⟨33695002812582551858215565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22463335208388367905477043 33695002812582551858215565)
                ·
                  refine ⟨12635626054718456946830837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33695002812582551858215565 12635626054718456946830837)
                  ·
                    refine ⟨1184589942629855338765391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12635626054718456946830837 1184589942629855338765391)
                    ·
                      rfl

theorem cell23_6920942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_6920942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6920942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6920942 prefixEnd_6920942 := by exact prefixLift 6920942
  have htrace : WordTrace (prefixWord ++ tailWord_6920942) baseStart_6920942 baseEnd_6920942 := by
    simpa [prefixWord, tailWord_6920942, baseEnd_6920942] using wordTrace_append hprefix tailTrace_6920942
  have hstable : (prefixWord ++ tailWord_6920942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6920942).length < 2 ^ (prefixWord ++ tailWord_6920942).sum := by decide
  have hdescent : baseEnd_6920942 < baseStart_6920942 := by decide
  rcases family_descends (prefixWord ++ tailWord_6920942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6920956 : List Nat := [2, 2, 2, 1, 3, 2, 1, 5, 1, 1, 3]
def baseStart_6920956 : Nat := 118140960795 + 6920956 * 2 ^ 59
def prefixEnd_6920956 : Nat := 4983230072969 + 3 ^ 40 * 6920956 * 2
def baseEnd_6920956 : Nat := 3553777016618728961521109

theorem tailTrace_6920956 : CollatzResearch.WordTrace tailWord_6920956 prefixEnd_6920956 3553777016618728961521109 := by
  unfold tailWord_6920956
  simp only [CollatzResearch.WordTrace]
  refine ⟨126214001557282946012835361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168285335409710594683780481 126214001557282946012835361)
  ·
    refine ⟨94660501167962209509626521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126214001557282946012835361 94660501167962209509626521)
    ·
      refine ⟨70995375875971657132219891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94660501167962209509626521 70995375875971657132219891)
      ·
        refine ⟨106493063813957485698329837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70995375875971657132219891 106493063813957485698329837)
        ·
          refine ⟨39934898930234057136873689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106493063813957485698329837 39934898930234057136873689)
          ·
            refine ⟨29951174197675542852655267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39934898930234057136873689 29951174197675542852655267)
            ·
              refine ⟨44926761296513314278982901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29951174197675542852655267 44926761296513314278982901)
              ·
                refine ⟨4211883871548123213654647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44926761296513314278982901 4211883871548123213654647)
                ·
                  refine ⟨6317825807322184820481971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4211883871548123213654647 6317825807322184820481971)
                  ·
                    refine ⟨9476738710983277230722957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6317825807322184820481971 9476738710983277230722957)
                    ·
                      refine ⟨3553777016618728961521109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9476738710983277230722957 3553777016618728961521109)
                      ·
                        rfl

theorem cell23_6920956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 5, 1, 1, 3].length) (baseStart_6920956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6920956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6920956 prefixEnd_6920956 := by exact prefixLift 6920956
  have htrace : WordTrace (prefixWord ++ tailWord_6920956) baseStart_6920956 baseEnd_6920956 := by
    simpa [prefixWord, tailWord_6920956, baseEnd_6920956] using wordTrace_append hprefix tailTrace_6920956
  have hstable : (prefixWord ++ tailWord_6920956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6920956).length < 2 ^ (prefixWord ++ tailWord_6920956).sum := by decide
  have hdescent : baseEnd_6920956 < baseStart_6920956 := by decide
  rcases family_descends (prefixWord ++ tailWord_6920956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6920965 : List Nat := [1, 3, 1, 1, 2, 1, 1, 2, 5, 1, 5]
def baseStart_6920965 : Nat := 118140960795 + 6920965 * 2 ^ 59
def prefixEnd_6920965 : Nat := 4983230072969 + 3 ^ 40 * 6920965 * 2
def baseEnd_6920965 : Nat := 3553781637944619426308567

theorem tailTrace_6920965 : CollatzResearch.WordTrace tailWord_6920965 prefixEnd_6920965 3553781637944619426308567 := by
  unfold tailWord_6920965
  simp only [CollatzResearch.WordTrace]
  refine ⟨252428331371533286562748349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168285554247688857708498899 252428331371533286562748349)
  ·
    refine ⟨94660624264324982461030631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252428331371533286562748349 94660624264324982461030631)
    ·
      refine ⟨141990936396487473691545947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94660624264324982461030631 141990936396487473691545947)
      ·
        refine ⟨212986404594731210537318921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141990936396487473691545947 212986404594731210537318921)
        ·
          refine ⟨159739803446048407902989191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212986404594731210537318921 159739803446048407902989191)
          ·
            refine ⟨239609705169072611854483787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159739803446048407902989191 239609705169072611854483787)
            ·
              refine ⟨359414557753608917781725681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239609705169072611854483787 359414557753608917781725681)
              ·
                refine ⟨269560918315206688336294261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 359414557753608917781725681 269560918315206688336294261)
                ·
                  refine ⟨25271336092050627031527587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 269560918315206688336294261 25271336092050627031527587)
                  ·
                    refine ⟨37907004138075940547291381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25271336092050627031527587 37907004138075940547291381)
                    ·
                      refine ⟨3553781637944619426308567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37907004138075940547291381 3553781637944619426308567)
                      ·
                        rfl

theorem cell23_6920965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 5, 1, 5].length) (baseStart_6920965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6920965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6920965 prefixEnd_6920965 := by exact prefixLift 6920965
  have htrace : WordTrace (prefixWord ++ tailWord_6920965) baseStart_6920965 baseEnd_6920965 := by
    simpa [prefixWord, tailWord_6920965, baseEnd_6920965] using wordTrace_append hprefix tailTrace_6920965
  have hstable : (prefixWord ++ tailWord_6920965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6920965).length < 2 ^ (prefixWord ++ tailWord_6920965).sum := by decide
  have hdescent : baseEnd_6920965 < baseStart_6920965 := by decide
  rcases family_descends (prefixWord ++ tailWord_6920965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6920975 : List Nat := [1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 6]
def baseStart_6920975 : Nat := 118140960795 + 6920975 * 2 ^ 59
def prefixEnd_6920975 : Nat := 4983230072969 + 3 ^ 40 * 6920975 * 2
def baseEnd_6920975 : Nat := 3553786772751164387183521

theorem tailTrace_6920975 : CollatzResearch.WordTrace tailWord_6920975 prefixEnd_6920975 3553786772751164387183521 := by
  unfold tailWord_6920975
  simp only [CollatzResearch.WordTrace]
  refine ⟨252428696101497058270612379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168285797400998038847074919 252428696101497058270612379)
  ·
    refine ⟨378643044152245587405918569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252428696101497058270612379 378643044152245587405918569)
    ·
      refine ⟨283982283114184190554438927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 378643044152245587405918569 283982283114184190554438927)
      ·
        refine ⟨425973424671276285831658391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283982283114184190554438927 425973424671276285831658391)
        ·
          refine ⟨638960137006914428747487587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425973424671276285831658391 638960137006914428747487587)
          ·
            refine ⟨958440205510371643121231381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 638960137006914428747487587 958440205510371643121231381)
            ·
              refine ⟨44926884633298670771307721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 958440205510371643121231381 44926884633298670771307721)
              ·
                refine ⟨33695163474974003078480791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44926884633298670771307721 33695163474974003078480791)
                ·
                  refine ⟨50542745212461004617721187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33695163474974003078480791 50542745212461004617721187)
                  ·
                    refine ⟨75814117818691506926581781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50542745212461004617721187 75814117818691506926581781)
                    ·
                      refine ⟨3553786772751164387183521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75814117818691506926581781 3553786772751164387183521)
                      ·
                        rfl

theorem cell23_6920975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 6].length) (baseStart_6920975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6920975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6920975 prefixEnd_6920975 := by exact prefixLift 6920975
  have htrace : WordTrace (prefixWord ++ tailWord_6920975) baseStart_6920975 baseEnd_6920975 := by
    simpa [prefixWord, tailWord_6920975, baseEnd_6920975] using wordTrace_append hprefix tailTrace_6920975
  have hstable : (prefixWord ++ tailWord_6920975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6920975).length < 2 ^ (prefixWord ++ tailWord_6920975).sum := by decide
  have hdescent : baseEnd_6920975 < baseStart_6920975 := by decide
  rcases family_descends (prefixWord ++ tailWord_6920975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6920992 : List Nat := [2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 6]
def baseStart_6920992 : Nat := 118140960795 + 6920992 * 2 ^ 59
def prefixEnd_6920992 : Nat := 4983230072969 + 3 ^ 40 * 6920992 * 2
def baseEnd_6920992 : Nat := 3553795501922290820670943

theorem tailTrace_6920992 : CollatzResearch.WordTrace tailWord_6920992 prefixEnd_6920992 3553795501922290820670943 := by
  unfold tailWord_6920992
  simp only [CollatzResearch.WordTrace]
  refine ⟨126214658071217735086990615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168286210761623646782654153 126214658071217735086990615)
  ·
    refine ⟨189321987106826602630485923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126214658071217735086990615 189321987106826602630485923)
    ·
      refine ⟨283982980660239903945728885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189321987106826602630485923 283982980660239903945728885)
      ·
        refine ⟨26623404436897490994912083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 283982980660239903945728885 26623404436897490994912083)
        ·
          refine ⟨39935106655346236492368125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26623404436897490994912083 39935106655346236492368125)
          ·
            refine ⟨14975664995754838684638047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39935106655346236492368125 14975664995754838684638047)
            ·
              refine ⟨22463497493632258026957071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14975664995754838684638047 22463497493632258026957071)
              ·
                refine ⟨33695246240448387040435607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22463497493632258026957071 33695246240448387040435607)
                ·
                  refine ⟨50542869360672580560653411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33695246240448387040435607 50542869360672580560653411)
                  ·
                    refine ⟨75814304041008870840980117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50542869360672580560653411 75814304041008870840980117)
                    ·
                      refine ⟨3553795501922290820670943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75814304041008870840980117 3553795501922290820670943)
                      ·
                        rfl

theorem cell23_6920992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_6920992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6920992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6920992 prefixEnd_6920992 := by exact prefixLift 6920992
  have htrace : WordTrace (prefixWord ++ tailWord_6920992) baseStart_6920992 baseEnd_6920992 := by
    simpa [prefixWord, tailWord_6920992, baseEnd_6920992] using wordTrace_append hprefix tailTrace_6920992
  have hstable : (prefixWord ++ tailWord_6920992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6920992).length < 2 ^ (prefixWord ++ tailWord_6920992).sum := by decide
  have hdescent : baseEnd_6920992 < baseStart_6920992 := by decide
  rcases family_descends (prefixWord ++ tailWord_6920992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6920996 : List Nat := [2, 3, 1, 3, 3, 1, 2, 2, 1, 1, 4]
def baseStart_6920996 : Nat := 118140960795 + 6920996 * 2 ^ 59
def prefixEnd_6920996 : Nat := 4983230072969 + 3 ^ 40 * 6920996 * 2
def baseEnd_6920996 : Nat := 3553797555844908805020925

theorem tailTrace_6920996 : CollatzResearch.WordTrace tailWord_6920996 prefixEnd_6920996 3553797555844908805020925 := by
  unfold tailWord_6920996
  simp only [CollatzResearch.WordTrace]
  refine ⟨126214731017210489428563421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168286308022947319238084561 126214731017210489428563421)
  ·
    refine ⟨47330524131453933535711283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126214731017210489428563421 47330524131453933535711283)
    ·
      refine ⟨70995786197180900303566925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47330524131453933535711283 70995786197180900303566925)
      ·
        refine ⟨26623419823942837613837597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70995786197180900303566925 26623419823942837613837597)
        ·
          refine ⟨9983782433978564105189099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26623419823942837613837597 9983782433978564105189099)
          ·
            refine ⟨14975673650967846157783649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9983782433978564105189099 14975673650967846157783649)
            ·
              refine ⟨11231755238225884618337737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14975673650967846157783649 11231755238225884618337737)
              ·
                refine ⟨8423816428669413463753303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11231755238225884618337737 8423816428669413463753303)
                ·
                  refine ⟨12635724643004120195629955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8423816428669413463753303 12635724643004120195629955)
                  ·
                    refine ⟨18953586964506180293444933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12635724643004120195629955 18953586964506180293444933)
                    ·
                      refine ⟨3553797555844908805020925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18953586964506180293444933 3553797555844908805020925)
                      ·
                        rfl

theorem cell23_6920996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_6920996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6920996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6920996 prefixEnd_6920996 := by exact prefixLift 6920996
  have htrace : WordTrace (prefixWord ++ tailWord_6920996) baseStart_6920996 baseEnd_6920996 := by
    simpa [prefixWord, tailWord_6920996, baseEnd_6920996] using wordTrace_append hprefix tailTrace_6920996
  have hstable : (prefixWord ++ tailWord_6920996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6920996).length < 2 ^ (prefixWord ++ tailWord_6920996).sum := by decide
  have hdescent : baseEnd_6920996 < baseStart_6920996 := by decide
  rcases family_descends (prefixWord ++ tailWord_6920996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6921072 : List Nat := [2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 5]
def baseStart_6921072 : Nat := 118140960795 + 6921072 * 2 ^ 59
def prefixEnd_6921072 : Nat := 4983230072969 + 3 ^ 40 * 6921072 * 2
def baseEnd_6921072 : Nat := 3553836580374650507670575

theorem tailTrace_6921072 : CollatzResearch.WordTrace tailWord_6921072 prefixEnd_6921072 3553836580374650507670575 := by
  unfold tailWord_6921072
  simp only [CollatzResearch.WordTrace]
  refine ⟨126216116991072821918446735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168288155988097095891262313 126216116991072821918446735)
  ·
    refine ⟨189324175486609232877670103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126216116991072821918446735 189324175486609232877670103)
    ·
      refine ⟨283986263229913849316505155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189324175486609232877670103 283986263229913849316505155)
      ·
        refine ⟨425979394844870773974757733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283986263229913849316505155 425979394844870773974757733)
        ·
          refine ⟨79871136533413270120267075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 425979394844870773974757733 79871136533413270120267075)
          ·
            refine ⟨119806704800119905180400613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79871136533413270120267075 119806704800119905180400613)
            ·
              refine ⟨22463757150022482221325115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119806704800119905180400613 22463757150022482221325115)
              ·
                refine ⟨33695635725033723331987673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22463757150022482221325115 33695635725033723331987673)
                ·
                  refine ⟨25271726793775292498990755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33695635725033723331987673 25271726793775292498990755)
                  ·
                    refine ⟨37907590190662938748486133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25271726793775292498990755 37907590190662938748486133)
                    ·
                      refine ⟨3553836580374650507670575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37907590190662938748486133 3553836580374650507670575)
                      ·
                        rfl

theorem cell23_6921072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 5].length) (baseStart_6921072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6921072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6921072 prefixEnd_6921072 := by exact prefixLift 6921072
  have htrace : WordTrace (prefixWord ++ tailWord_6921072) baseStart_6921072 baseEnd_6921072 := by
    simpa [prefixWord, tailWord_6921072, baseEnd_6921072] using wordTrace_append hprefix tailTrace_6921072
  have hstable : (prefixWord ++ tailWord_6921072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6921072).length < 2 ^ (prefixWord ++ tailWord_6921072).sum := by decide
  have hdescent : baseEnd_6921072 < baseStart_6921072 := by decide
  rcases family_descends (prefixWord ++ tailWord_6921072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6921073 : List Nat := [1, 2, 2, 2, 1, 5, 3, 1, 1, 3, 2]
def baseStart_6921073 : Nat := 118140960795 + 6921073 * 2 ^ 59
def prefixEnd_6921073 : Nat := 4983230072969 + 3 ^ 40 * 6921073 * 2
def baseEnd_6921073 : Nat := 3553837093855305003758071

theorem tailTrace_6921073 : CollatzResearch.WordTrace tailWord_6921073 prefixEnd_6921073 3553837093855305003758071 := by
  unfold tailWord_6921073
  simp only [CollatzResearch.WordTrace]
  refine ⟨252432270455142021007679873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168288180303428014005119915 252432270455142021007679873)
  ·
    refine ⟨189324202841356515755759905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252432270455142021007679873 189324202841356515755759905)
    ·
      refine ⟨141993152131017386816819929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189324202841356515755759905 141993152131017386816819929)
      ·
        refine ⟨106494864098263040112614947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141993152131017386816819929 106494864098263040112614947)
        ·
          refine ⟨159742296147394560168922421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106494864098263040112614947 159742296147394560168922421)
          ·
            refine ⟨14975840263818240015836477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 159742296147394560168922421 14975840263818240015836477)
            ·
              refine ⟨5615940098931840005938679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14975840263818240015836477 5615940098931840005938679)
              ·
                refine ⟨8423910148397760008908019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5615940098931840005938679 8423910148397760008908019)
                ·
                  refine ⟨12635865222596640013362029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8423910148397760008908019 12635865222596640013362029)
                  ·
                    refine ⟨4738449458473740005010761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12635865222596640013362029 4738449458473740005010761)
                    ·
                      refine ⟨3553837093855305003758071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4738449458473740005010761 3553837093855305003758071)
                      ·
                        rfl

theorem cell23_6921073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 3, 1, 1, 3, 2].length) (baseStart_6921073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6921073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6921073 prefixEnd_6921073 := by exact prefixLift 6921073
  have htrace : WordTrace (prefixWord ++ tailWord_6921073) baseStart_6921073 baseEnd_6921073 := by
    simpa [prefixWord, tailWord_6921073, baseEnd_6921073] using wordTrace_append hprefix tailTrace_6921073
  have hstable : (prefixWord ++ tailWord_6921073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6921073).length < 2 ^ (prefixWord ++ tailWord_6921073).sum := by decide
  have hdescent : baseEnd_6921073 < baseStart_6921073 := by decide
  rcases family_descends (prefixWord ++ tailWord_6921073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6921082 : List Nat := [3, 1, 1, 1, 1, 1, 3, 4, 2, 2, 4]
def baseStart_6921082 : Nat := 118140960795 + 6921082 * 2 ^ 59
def prefixEnd_6921082 : Nat := 4983230072969 + 3 ^ 40 * 6921082 * 2
def baseEnd_6921082 : Nat := 3553841715181195468545529

theorem tailTrace_6921082 : CollatzResearch.WordTrace tailWord_6921082 prefixEnd_6921082 3553841715181195468545529 := by
  unfold tailWord_6921082
  simp only [CollatzResearch.WordTrace]
  refine ⟨63108149678027353886189375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168288399141406277029838333 63108149678027353886189375)
  ·
    refine ⟨94662224517041030829284063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63108149678027353886189375 94662224517041030829284063)
    ·
      refine ⟨141993336775561546243926095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94662224517041030829284063 141993336775561546243926095)
      ·
        refine ⟨212990005163342319365889143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141993336775561546243926095 212990005163342319365889143)
        ·
          refine ⟨319485007745013479048833715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212990005163342319365889143 319485007745013479048833715)
          ·
            refine ⟨479227511617520218573250573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319485007745013479048833715 479227511617520218573250573)
            ·
              refine ⟨179710316856570081964968965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 479227511617520218573250573 179710316856570081964968965)
              ·
                refine ⟨33695684410606890368431681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 179710316856570081964968965 33695684410606890368431681)
                ·
                  refine ⟨25271763307955167776323761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33695684410606890368431681 25271763307955167776323761)
                  ·
                    refine ⟨18953822480966375832242821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25271763307955167776323761 18953822480966375832242821)
                    ·
                      refine ⟨3553841715181195468545529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18953822480966375832242821 3553841715181195468545529)
                      ·
                        rfl

theorem cell23_6921082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 2, 2, 4].length) (baseStart_6921082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6921082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6921082 prefixEnd_6921082 := by exact prefixLift 6921082
  have htrace : WordTrace (prefixWord ++ tailWord_6921082) baseStart_6921082 baseEnd_6921082 := by
    simpa [prefixWord, tailWord_6921082, baseEnd_6921082] using wordTrace_append hprefix tailTrace_6921082
  have hstable : (prefixWord ++ tailWord_6921082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6921082).length < 2 ^ (prefixWord ++ tailWord_6921082).sum := by decide
  have hdescent : baseEnd_6921082 < baseStart_6921082 := by decide
  rcases family_descends (prefixWord ++ tailWord_6921082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6921092 : List Nat := [2, 3, 2, 1, 1, 1, 1, 5, 7]
def baseStart_6921092 : Nat := 118140960795 + 6921092 * 2 ^ 59
def prefixEnd_6921092 : Nat := 4983230072969 + 3 ^ 40 * 6921092 * 2
def baseEnd_6921092 : Nat := 394871872220860047713387

theorem tailTrace_6921092 : CollatzResearch.WordTrace tailWord_6921092 prefixEnd_6921092 394871872220860047713387 := by
  unfold tailWord_6921092
  simp only [CollatzResearch.WordTrace]
  refine ⟨126216481721036593626310765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168288642294715458168414353 126216481721036593626310765)
  ·
    refine ⟨47331180645388722609866537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126216481721036593626310765 47331180645388722609866537)
    ·
      refine ⟨35498385484041541957399903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47331180645388722609866537 35498385484041541957399903)
      ·
        refine ⟨53247578226062312936099855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35498385484041541957399903 53247578226062312936099855)
        ·
          refine ⟨79871367339093469404149783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53247578226062312936099855 79871367339093469404149783)
          ·
            refine ⟨119807051008640204106224675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79871367339093469404149783 119807051008640204106224675)
            ·
              refine ⟨179710576512960306159337013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119807051008640204106224675 179710576512960306159337013)
              ·
                refine ⟨16847866548090028702437845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 179710576512960306159337013 16847866548090028702437845)
                ·
                  refine ⟨394871872220860047713387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16847866548090028702437845 394871872220860047713387)
                  ·
                    rfl

theorem cell23_6921092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 5, 7].length) (baseStart_6921092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6921092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6921092 prefixEnd_6921092 := by exact prefixLift 6921092
  have htrace : WordTrace (prefixWord ++ tailWord_6921092) baseStart_6921092 baseEnd_6921092 := by
    simpa [prefixWord, tailWord_6921092, baseEnd_6921092] using wordTrace_append hprefix tailTrace_6921092
  have hstable : (prefixWord ++ tailWord_6921092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6921092).length < 2 ^ (prefixWord ++ tailWord_6921092).sum := by decide
  have hdescent : baseEnd_6921092 < baseStart_6921092 := by decide
  rcases family_descends (prefixWord ++ tailWord_6921092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6921137 : List Nat := [1, 2, 2, 4, 4, 1, 1, 2, 2, 2, 2]
def baseStart_6921137 : Nat := 118140960795 + 6921137 * 2 ^ 59
def prefixEnd_6921137 : Nat := 4983230072969 + 3 ^ 40 * 6921137 * 2
def baseEnd_6921137 : Nat := 3553869956617192753357777

theorem tailTrace_6921137 : CollatzResearch.WordTrace tailWord_6921137 prefixEnd_6921137 3553869956617192753357777 := by
  unfold tailWord_6921137
  simp only [CollatzResearch.WordTrace]
  refine ⟨252434604726910159938009665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168289736484606773292006443 252434604726910159938009665)
  ·
    refine ⟨189325953545182619953507249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252434604726910159938009665 189325953545182619953507249)
    ·
      refine ⟨141994465158886964965130437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189325953545182619953507249 141994465158886964965130437)
      ·
        refine ⟨26623962217291305930961957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141994465158886964965130437 26623962217291305930961957)
        ·
          refine ⟨4991992915742119862055367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26623962217291305930961957 4991992915742119862055367)
          ·
            refine ⟨7487989373613179793083051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4991992915742119862055367 7487989373613179793083051)
            ·
              refine ⟨11231984060419769689624577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7487989373613179793083051 11231984060419769689624577)
              ·
                refine ⟨8423988045314827267218433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11231984060419769689624577 8423988045314827267218433)
                ·
                  refine ⟨6317991033986120450413825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8423988045314827267218433 6317991033986120450413825)
                  ·
                    refine ⟨4738493275489590337810369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6317991033986120450413825 4738493275489590337810369)
                    ·
                      refine ⟨3553869956617192753357777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4738493275489590337810369 3553869956617192753357777)
                      ·
                        rfl

theorem cell23_6921137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 2, 2, 2, 2].length) (baseStart_6921137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6921137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6921137 prefixEnd_6921137 := by exact prefixLift 6921137
  have htrace : WordTrace (prefixWord ++ tailWord_6921137) baseStart_6921137 baseEnd_6921137 := by
    simpa [prefixWord, tailWord_6921137, baseEnd_6921137] using wordTrace_append hprefix tailTrace_6921137
  have hstable : (prefixWord ++ tailWord_6921137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6921137).length < 2 ^ (prefixWord ++ tailWord_6921137).sum := by decide
  have hdescent : baseEnd_6921137 < baseStart_6921137 := by decide
  rcases family_descends (prefixWord ++ tailWord_6921137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6921169 : List Nat := [1, 2, 2, 1, 2, 1, 3, 4, 3, 4]
def baseStart_6921169 : Nat := 118140960795 + 6921169 * 2 ^ 59
def prefixEnd_6921169 : Nat := 4983230072969 + 3 ^ 40 * 6921169 * 2
def baseEnd_6921169 : Nat := 1184628795999378876052543

theorem tailTrace_6921169 : CollatzResearch.WordTrace tailWord_6921169 prefixEnd_6921169 1184628795999378876052543 := by
  unfold tailWord_6921169
  simp only [CollatzResearch.WordTrace]
  refine ⟨252435771862794229403174561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168290514575196152935449707 252435771862794229403174561)
  ·
    refine ⟨189326828897095672052380921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252435771862794229403174561 189326828897095672052380921)
    ·
      refine ⟨141995121672821754039285691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189326828897095672052380921 141995121672821754039285691)
      ·
        refine ⟨212992682509232631058928537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141995121672821754039285691 212992682509232631058928537)
        ·
          refine ⟨159744511881924473294196403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212992682509232631058928537 159744511881924473294196403)
          ·
            refine ⟨239616767822886709941294605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159744511881924473294196403 239616767822886709941294605)
            ·
              refine ⟨89856287933582516227985477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 239616767822886709941294605 89856287933582516227985477)
              ·
                refine ⟨16848053987546721792747277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89856287933582516227985477 16848053987546721792747277)
                ·
                  refine ⟨6318020245330020672280229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16848053987546721792747277 6318020245330020672280229)
                  ·
                    refine ⟨1184628795999378876052543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6318020245330020672280229 1184628795999378876052543)
                    ·
                      rfl

theorem cell23_6921169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 4, 3, 4].length) (baseStart_6921169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6921169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6921169 prefixEnd_6921169 := by exact prefixLift 6921169
  have htrace : WordTrace (prefixWord ++ tailWord_6921169) baseStart_6921169 baseEnd_6921169 := by
    simpa [prefixWord, tailWord_6921169, baseEnd_6921169] using wordTrace_append hprefix tailTrace_6921169
  have hstable : (prefixWord ++ tailWord_6921169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6921169).length < 2 ^ (prefixWord ++ tailWord_6921169).sum := by decide
  have hdescent : baseEnd_6921169 < baseStart_6921169 := by decide
  rcases family_descends (prefixWord ++ tailWord_6921169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6921269 : List Nat := [1, 3, 3, 1, 1, 1, 1, 3, 3, 1, 5]
def baseStart_6921269 : Nat := 118140960795 + 6921269 * 2 ^ 59
def prefixEnd_6921269 : Nat := 4983230072969 + 3 ^ 40 * 6921269 * 2
def baseEnd_6921269 : Nat := 3553937736063586236907169

theorem tailTrace_6921269 : CollatzResearch.WordTrace tailWord_6921269 prefixEnd_6921269 3553937736063586236907169 := by
  unfold tailWord_6921269
  simp only [CollatzResearch.WordTrace]
  refine ⟨252439419162431946481814861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168292946108287964321209907 252439419162431946481814861)
  ·
    refine ⟨94664782185911979930680573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252439419162431946481814861 94664782185911979930680573)
    ·
      refine ⟨35499293319716992474005215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94664782185911979930680573 35499293319716992474005215)
      ·
        refine ⟨53248939979575488711007823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35499293319716992474005215 53248939979575488711007823)
        ·
          refine ⟨79873409969363233066511735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53248939979575488711007823 79873409969363233066511735)
          ·
            refine ⟨119810114954044849599767603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79873409969363233066511735 119810114954044849599767603)
            ·
              refine ⟨179715172431067274399651405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119810114954044849599767603 179715172431067274399651405)
              ·
                refine ⟨67393189661650227899869277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 179715172431067274399651405 67393189661650227899869277)
                ·
                  refine ⟨25272446123118835462450979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67393189661650227899869277 25272446123118835462450979)
                  ·
                    refine ⟨37908669184678253193676469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25272446123118835462450979 37908669184678253193676469)
                    ·
                      refine ⟨3553937736063586236907169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37908669184678253193676469 3553937736063586236907169)
                      ·
                        rfl

theorem cell23_6921269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_6921269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6921269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6921269 prefixEnd_6921269 := by exact prefixLift 6921269
  have htrace : WordTrace (prefixWord ++ tailWord_6921269) baseStart_6921269 baseEnd_6921269 := by
    simpa [prefixWord, tailWord_6921269, baseEnd_6921269] using wordTrace_append hprefix tailTrace_6921269
  have hstable : (prefixWord ++ tailWord_6921269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6921269).length < 2 ^ (prefixWord ++ tailWord_6921269).sum := by decide
  have hdescent : baseEnd_6921269 < baseStart_6921269 := by decide
  rcases family_descends (prefixWord ++ tailWord_6921269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6921276 : List Nat := [2, 2, 2, 2, 2, 3, 2, 1, 1, 6]
def baseStart_6921276 : Nat := 118140960795 + 6921276 * 2 ^ 59
def prefixEnd_6921276 : Nat := 4983230072969 + 3 ^ 40 * 6921276 * 2
def baseEnd_6921276 : Nat := 1184647110142722569839879

theorem tailTrace_6921276 : CollatzResearch.WordTrace tailWord_6921276 prefixEnd_6921276 1184647110142722569839879 := by
  unfold tailWord_6921276
  simp only [CollatzResearch.WordTrace]
  refine ⟨126219837236703293338659841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168293116315604391118213121 126219837236703293338659841)
  ·
    refine ⟨94664877927527470003994881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126219837236703293338659841 94664877927527470003994881)
    ·
      refine ⟨70998658445645602502996161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94664877927527470003994881 70998658445645602502996161)
      ·
        refine ⟨53248993834234201877247121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70998658445645602502996161 53248993834234201877247121)
        ·
          refine ⟨39936745375675651407935341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53248993834234201877247121 39936745375675651407935341)
          ·
            refine ⟨14976279515878369277975753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39936745375675651407935341 14976279515878369277975753)
            ·
              refine ⟨11232209636908776958481815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14976279515878369277975753 11232209636908776958481815)
              ·
                refine ⟨16848314455363165437722723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11232209636908776958481815 16848314455363165437722723)
                ·
                  refine ⟨25272471683044748156584085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16848314455363165437722723 25272471683044748156584085)
                  ·
                    refine ⟨1184647110142722569839879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25272471683044748156584085 1184647110142722569839879)
                    ·
                      rfl

theorem cell23_6921276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 1, 1, 6].length) (baseStart_6921276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6921276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6921276 prefixEnd_6921276 := by exact prefixLift 6921276
  have htrace : WordTrace (prefixWord ++ tailWord_6921276) baseStart_6921276 baseEnd_6921276 := by
    simpa [prefixWord, tailWord_6921276, baseEnd_6921276] using wordTrace_append hprefix tailTrace_6921276
  have hstable : (prefixWord ++ tailWord_6921276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6921276).length < 2 ^ (prefixWord ++ tailWord_6921276).sum := by decide
  have hdescent : baseEnd_6921276 < baseStart_6921276 := by decide
  rcases family_descends (prefixWord ++ tailWord_6921276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6921283 : List Nat := [1, 1, 1, 3, 1, 2, 5, 2, 3, 2, 2]
def baseStart_6921283 : Nat := 118140960795 + 6921283 * 2 ^ 59
def prefixEnd_6921283 : Nat := 4983230072969 + 3 ^ 40 * 6921283 * 2
def baseEnd_6921283 : Nat := 3553944924792749182132105

theorem tailTrace_6921283 : CollatzResearch.WordTrace tailWord_6921283 prefixEnd_6921283 3553944924792749182132105 := by
  unfold tailWord_6921283
  simp only [CollatzResearch.WordTrace]
  refine ⟨252439929784381226872824503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168293286522920817915216335 252439929784381226872824503)
  ·
    refine ⟨378659894676571840309236755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252439929784381226872824503 378659894676571840309236755)
    ·
      refine ⟨567989842014857760463855133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378659894676571840309236755 567989842014857760463855133)
      ·
        refine ⟨212996190755571660173945675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 567989842014857760463855133 212996190755571660173945675)
        ·
          refine ⟨319494286133357490260918513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212996190755571660173945675 319494286133357490260918513)
          ·
            refine ⟨239620714600018117695688885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 319494286133357490260918513 239620714600018117695688885)
            ·
              refine ⟨22464441993751698533970833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 239620714600018117695688885 22464441993751698533970833)
              ·
                refine ⟨16848331495313773900478125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22464441993751698533970833 16848331495313773900478125)
                ·
                  refine ⟨6318124310742665212679297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16848331495313773900478125 6318124310742665212679297)
                  ·
                    refine ⟨4738593233056998909509473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6318124310742665212679297 4738593233056998909509473)
                    ·
                      refine ⟨3553944924792749182132105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4738593233056998909509473 3553944924792749182132105)
                      ·
                        rfl

theorem cell23_6921283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 2, 3, 2, 2].length) (baseStart_6921283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6921283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6921283 prefixEnd_6921283 := by exact prefixLift 6921283
  have htrace : WordTrace (prefixWord ++ tailWord_6921283) baseStart_6921283 baseEnd_6921283 := by
    simpa [prefixWord, tailWord_6921283, baseEnd_6921283] using wordTrace_append hprefix tailTrace_6921283
  have hstable : (prefixWord ++ tailWord_6921283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6921283).length < 2 ^ (prefixWord ++ tailWord_6921283).sum := by decide
  have hdescent : baseEnd_6921283 < baseStart_6921283 := by decide
  rcases family_descends (prefixWord ++ tailWord_6921283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6921339 : List Nat := [1, 1, 1, 1, 1, 4, 1, 4, 2, 3, 4]
def baseStart_6921339 : Nat := 118140960795 + 6921339 * 2 ^ 59
def prefixEnd_6921339 : Nat := 4983230072969 + 3 ^ 40 * 6921339 * 2
def baseEnd_6921339 : Nat := 3553973679709400963031847

theorem tailTrace_6921339 : CollatzResearch.WordTrace tailWord_6921339 prefixEnd_6921339 3553973679709400963031847 := by
  unfold tailWord_6921339
  simp only [CollatzResearch.WordTrace]
  refine ⟨252441972272178348436863071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168294648181452232291242047 252441972272178348436863071)
  ·
    refine ⟨378662958408267522655294607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252441972272178348436863071 378662958408267522655294607)
    ·
      refine ⟨567994437612401283982941911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378662958408267522655294607 567994437612401283982941911)
      ·
        refine ⟨851991656418601925974412867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 567994437612401283982941911 851991656418601925974412867)
        ·
          refine ⟨1277987484627902888961619301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 851991656418601925974412867 1277987484627902888961619301)
          ·
            refine ⟨239622653367731791680303619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1277987484627902888961619301 239622653367731791680303619)
            ·
              refine ⟨359433980051597687520455429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239622653367731791680303619 359433980051597687520455429)
              ·
                refine ⟨67393871259674566410085393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 359433980051597687520455429 67393871259674566410085393)
                ·
                  refine ⟨50545403444755924807564045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67393871259674566410085393 50545403444755924807564045)
                  ·
                    refine ⟨18954526291783471802836517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50545403444755924807564045 18954526291783471802836517)
                    ·
                      refine ⟨3553973679709400963031847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18954526291783471802836517 3553973679709400963031847)
                      ·
                        rfl

theorem cell23_6921339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 3, 4].length) (baseStart_6921339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6921339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6921339 prefixEnd_6921339 := by exact prefixLift 6921339
  have htrace : WordTrace (prefixWord ++ tailWord_6921339) baseStart_6921339 baseEnd_6921339 := by
    simpa [prefixWord, tailWord_6921339, baseEnd_6921339] using wordTrace_append hprefix tailTrace_6921339
  have hstable : (prefixWord ++ tailWord_6921339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6921339).length < 2 ^ (prefixWord ++ tailWord_6921339).sum := by decide
  have hdescent : baseEnd_6921339 < baseStart_6921339 := by decide
  rcases family_descends (prefixWord ++ tailWord_6921339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6921376 : List Nat := [2, 1, 1, 4, 2, 1, 2, 1, 2, 4, 3]
def baseStart_6921376 : Nat := 118140960795 + 6921376 * 2 ^ 59
def prefixEnd_6921376 : Nat := 4983230072969 + 3 ^ 40 * 6921376 * 2
def baseEnd_6921376 : Nat := 3553992678493617318269177

theorem tailTrace_6921376 : CollatzResearch.WordTrace tailWord_6921376 prefixEnd_6921376 3553992678493617318269177 := by
  unfold tailWord_6921376
  simp only [CollatzResearch.WordTrace]
  refine ⟨126221660886522151877979991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168295547848696202503973321 126221660886522151877979991)
  ·
    refine ⟨189332491329783227816969987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126221660886522151877979991 189332491329783227816969987)
    ·
      refine ⟨283998736994674841725454981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189332491329783227816969987 283998736994674841725454981)
      ·
        refine ⟨53249763186501532823522809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 283998736994674841725454981 53249763186501532823522809)
        ·
          refine ⟨39937322389876149617642107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53249763186501532823522809 39937322389876149617642107)
          ·
            refine ⟨59905983584814224426463161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39937322389876149617642107 59905983584814224426463161)
            ·
              refine ⟨44929487688610668319847371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59905983584814224426463161 44929487688610668319847371)
              ·
                refine ⟨67394231532916002479771057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44929487688610668319847371 67394231532916002479771057)
                ·
                  refine ⟨50545673649687001859828293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67394231532916002479771057 50545673649687001859828293)
                  ·
                    refine ⟨9477313809316312848717805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50545673649687001859828293 9477313809316312848717805)
                    ·
                      refine ⟨3553992678493617318269177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9477313809316312848717805 3553992678493617318269177)
                      ·
                        rfl

theorem cell23_6921376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 2, 4, 3].length) (baseStart_6921376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6921376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6921376 prefixEnd_6921376 := by exact prefixLift 6921376
  have htrace : WordTrace (prefixWord ++ tailWord_6921376) baseStart_6921376 baseEnd_6921376 := by
    simpa [prefixWord, tailWord_6921376, baseEnd_6921376] using wordTrace_append hprefix tailTrace_6921376
  have hstable : (prefixWord ++ tailWord_6921376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6921376).length < 2 ^ (prefixWord ++ tailWord_6921376).sum := by decide
  have hdescent : baseEnd_6921376 < baseStart_6921376 := by decide
  rcases family_descends (prefixWord ++ tailWord_6921376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6921513 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 9, 1, 3]
def baseStart_6921513 : Nat := 118140960795 + 6921513 * 2 ^ 59
def prefixEnd_6921513 : Nat := 4983230072969 + 3 ^ 40 * 6921513 * 2
def baseEnd_6921513 : Nat := 3554063025343283282256047

theorem tailTrace_6921513 : CollatzResearch.WordTrace tailWord_6921513 prefixEnd_6921513 3554063025343283282256047 := by
  unfold tailWord_6921513
  simp only [CollatzResearch.WordTrace]
  refine ⟨252448318573547976153697193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168298879049031984102464795 252448318573547976153697193)
  ·
    refine ⟨189336238930160982115272895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252448318573547976153697193 189336238930160982115272895)
    ·
      refine ⟨284004358395241473172909343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189336238930160982115272895 284004358395241473172909343)
      ·
        refine ⟨426006537592862209759364015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284004358395241473172909343 426006537592862209759364015)
        ·
          refine ⟨639009806389293314639046023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426006537592862209759364015 639009806389293314639046023)
          ·
            refine ⟨958514709583939971958569035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 639009806389293314639046023 958514709583939971958569035)
            ·
              refine ⟨1437772064375909957937853553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 958514709583939971958569035 1437772064375909957937853553)
              ·
                refine ⟨1078329048281932468453390165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1437772064375909957937853553 1078329048281932468453390165)
                ·
                  refine ⟨6318334267276948057344083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1078329048281932468453390165 6318334267276948057344083)
                  ·
                    refine ⟨9477501400915422086016125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6318334267276948057344083 9477501400915422086016125)
                    ·
                      refine ⟨3554063025343283282256047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9477501400915422086016125 3554063025343283282256047)
                      ·
                        rfl

theorem cell23_6921513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 9, 1, 3].length) (baseStart_6921513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6921513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6921513 prefixEnd_6921513 := by exact prefixLift 6921513
  have htrace : WordTrace (prefixWord ++ tailWord_6921513) baseStart_6921513 baseEnd_6921513 := by
    simpa [prefixWord, tailWord_6921513, baseEnd_6921513] using wordTrace_append hprefix tailTrace_6921513
  have hstable : (prefixWord ++ tailWord_6921513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6921513).length < 2 ^ (prefixWord ++ tailWord_6921513).sum := by decide
  have hdescent : baseEnd_6921513 < baseStart_6921513 := by decide
  rcases family_descends (prefixWord ++ tailWord_6921513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6921553 : List Nat := [1, 2, 2, 1, 4, 1, 2, 2, 3, 1, 4]
def baseStart_6921553 : Nat := 118140960795 + 6921553 * 2 ^ 59
def prefixEnd_6921553 : Nat := 4983230072969 + 3 ^ 40 * 6921553 * 2
def baseEnd_6921553 : Nat := 3554083564569463125755863

theorem tailTrace_6921553 : CollatzResearch.WordTrace tailWord_6921553 prefixEnd_6921553 3554083564569463125755863 := by
  unfold tailWord_6921553
  simp only [CollatzResearch.WordTrace]
  refine ⟨252449777493403062985153313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168299851662268708656768875 252449777493403062985153313)
  ·
    refine ⟨189337333120052297238864985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252449777493403062985153313 189337333120052297238864985)
    ·
      refine ⟨142002999840039222929148739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189337333120052297238864985 142002999840039222929148739)
      ·
        refine ⟨213004499760058834393723109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142002999840039222929148739 213004499760058834393723109)
        ·
          refine ⟨39938343705011031448823083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 213004499760058834393723109 39938343705011031448823083)
          ·
            refine ⟨59907515557516547173234625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39938343705011031448823083 59907515557516547173234625)
            ·
              refine ⟨44930636668137410379925969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59907515557516547173234625 44930636668137410379925969)
              ·
                refine ⟨33697977501103057784944477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44930636668137410379925969 33697977501103057784944477)
                ·
                  refine ⟨12636741562913646669354179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33697977501103057784944477 12636741562913646669354179)
                  ·
                    refine ⟨18955112344370470004031269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12636741562913646669354179 18955112344370470004031269)
                    ·
                      refine ⟨3554083564569463125755863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18955112344370470004031269 3554083564569463125755863)
                      ·
                        rfl

theorem cell23_6921553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 3, 1, 4].length) (baseStart_6921553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6921553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6921553 prefixEnd_6921553 := by exact prefixLift 6921553
  have htrace : WordTrace (prefixWord ++ tailWord_6921553) baseStart_6921553 baseEnd_6921553 := by
    simpa [prefixWord, tailWord_6921553, baseEnd_6921553] using wordTrace_append hprefix tailTrace_6921553
  have hstable : (prefixWord ++ tailWord_6921553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6921553).length < 2 ^ (prefixWord ++ tailWord_6921553).sum := by decide
  have hdescent : baseEnd_6921553 < baseStart_6921553 := by decide
  rcases family_descends (prefixWord ++ tailWord_6921553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6921570 : List Nat := [3, 3, 2, 1, 1, 1, 3, 1, 3, 1, 4]
def baseStart_6921570 : Nat := 118140960795 + 6921570 * 2 ^ 59
def prefixEnd_6921570 : Nat := 4983230072969 + 3 ^ 40 * 6921570 * 2
def baseEnd_6921570 : Nat := 3554092293740589559243285

theorem tailTrace_6921570 : CollatzResearch.WordTrace tailWord_6921570 prefixEnd_6921570 3554092293740589559243285 := by
  unfold tailWord_6921570
  simp only [CollatzResearch.WordTrace]
  refine ⟨63112599383585368722130541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168300265022894316592348109 63112599383585368722130541)
  ·
    refine ⟨23667224768844513270798953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63112599383585368722130541 23667224768844513270798953)
    ·
      refine ⟨17750418576633384953099215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23667224768844513270798953 17750418576633384953099215)
      ·
        refine ⟨26625627864950077429648823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17750418576633384953099215 26625627864950077429648823)
        ·
          refine ⟨39938441797425116144473235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26625627864950077429648823 39938441797425116144473235)
          ·
            refine ⟨59907662696137674216709853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39938441797425116144473235 59907662696137674216709853)
            ·
              refine ⟨22465373511051627831266195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59907662696137674216709853 22465373511051627831266195)
              ·
                refine ⟨33698060266577441746899293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22465373511051627831266195 33698060266577441746899293)
                ·
                  refine ⟨12636772599966540655087235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33698060266577441746899293 12636772599966540655087235)
                  ·
                    refine ⟨18955158899949810982630853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12636772599966540655087235 18955158899949810982630853)
                    ·
                      refine ⟨3554092293740589559243285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18955158899949810982630853 3554092293740589559243285)
                      ·
                        rfl

theorem cell23_6921570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_6921570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6921570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6921570 prefixEnd_6921570 := by exact prefixLift 6921570
  have htrace : WordTrace (prefixWord ++ tailWord_6921570) baseStart_6921570 baseEnd_6921570 := by
    simpa [prefixWord, tailWord_6921570, baseEnd_6921570] using wordTrace_append hprefix tailTrace_6921570
  have hstable : (prefixWord ++ tailWord_6921570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6921570).length < 2 ^ (prefixWord ++ tailWord_6921570).sum := by decide
  have hdescent : baseEnd_6921570 < baseStart_6921570 := by decide
  rcases family_descends (prefixWord ++ tailWord_6921570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6921583 : List Nat := [1, 1, 2, 1, 3, 1, 5, 2, 1, 2, 4]
def baseStart_6921583 : Nat := 118140960795 + 6921583 * 2 ^ 59
def prefixEnd_6921583 : Nat := 4983230072969 + 3 ^ 40 * 6921583 * 2
def baseEnd_6921583 : Nat := 3554098968989098008380725

theorem tailTrace_6921583 : CollatzResearch.WordTrace tailWord_6921583 prefixEnd_6921583 3554098968989098008380725 := by
  unfold tailWord_6921583
  simp only [CollatzResearch.WordTrace]
  refine ⟨252450871683294378108745403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168300581122196252072496935 252450871683294378108745403)
  ·
    refine ⟨378676307524941567163118105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252450871683294378108745403 378676307524941567163118105)
    ·
      refine ⟨284007230643706175372338579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 378676307524941567163118105 284007230643706175372338579)
      ·
        refine ⟨426010845965559263058507869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284007230643706175372338579 426010845965559263058507869)
        ·
          refine ⟨159754067237084723646940451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 426010845965559263058507869 159754067237084723646940451)
          ·
            refine ⟨239631100855627085470410677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159754067237084723646940451 239631100855627085470410677)
            ·
              refine ⟨22465415705215039262851001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 239631100855627085470410677 22465415705215039262851001)
              ·
                refine ⟨16849061778911279447138251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22465415705215039262851001 16849061778911279447138251)
                ·
                  refine ⟨25273592668366919170707377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16849061778911279447138251 25273592668366919170707377)
                  ·
                    refine ⟨18955194501275189378030533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25273592668366919170707377 18955194501275189378030533)
                    ·
                      refine ⟨3554098968989098008380725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18955194501275189378030533 3554098968989098008380725)
                      ·
                        rfl

theorem cell23_6921583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 2, 1, 2, 4].length) (baseStart_6921583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6921583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6921583 prefixEnd_6921583 := by exact prefixLift 6921583
  have htrace : WordTrace (prefixWord ++ tailWord_6921583) baseStart_6921583 baseEnd_6921583 := by
    simpa [prefixWord, tailWord_6921583, baseEnd_6921583] using wordTrace_append hprefix tailTrace_6921583
  have hstable : (prefixWord ++ tailWord_6921583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6921583).length < 2 ^ (prefixWord ++ tailWord_6921583).sum := by decide
  have hdescent : baseEnd_6921583 < baseStart_6921583 := by decide
  rcases family_descends (prefixWord ++ tailWord_6921583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6921598 : List Nat := [4, 2, 3, 2, 1, 1, 1, 4, 1, 1, 3]
def baseStart_6921598 : Nat := 118140960795 + 6921598 * 2 ^ 59
def prefixEnd_6921598 : Nat := 4983230072969 + 3 ^ 40 * 6921598 * 2
def baseEnd_6921598 : Nat := 3554106671198915449693157

theorem tailTrace_6921598 : CollatzResearch.WordTrace tailWord_6921598 prefixEnd_6921598 3554106671198915449693157 := by
  unfold tailWord_6921598
  simp only [CollatzResearch.WordTrace]
  refine ⟨31556427347280004458817681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168300945852160023780360965 31556427347280004458817681)
  ·
    refine ⟨23667320510460003344113261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31556427347280004458817681 23667320510460003344113261)
    ·
      refine ⟨8875245191422501254042473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23667320510460003344113261 8875245191422501254042473)
      ·
        refine ⟨6656433893566875940531855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8875245191422501254042473 6656433893566875940531855)
        ·
          refine ⟨9984650840350313910797783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6656433893566875940531855 9984650840350313910797783)
          ·
            refine ⟨14976976260525470866196675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9984650840350313910797783 14976976260525470866196675)
            ·
              refine ⟨22465464390788206299295013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14976976260525470866196675 22465464390788206299295013)
              ·
                refine ⟨4212274573272788681117815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22465464390788206299295013 4212274573272788681117815)
                ·
                  refine ⟨6318411859909183021676723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4212274573272788681117815 6318411859909183021676723)
                  ·
                    refine ⟨9477617789863774532515085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6318411859909183021676723 9477617789863774532515085)
                    ·
                      refine ⟨3554106671198915449693157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9477617789863774532515085 3554106671198915449693157)
                      ·
                        rfl

theorem cell23_6921598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_6921598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6921598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6921598 prefixEnd_6921598 := by exact prefixLift 6921598
  have htrace : WordTrace (prefixWord ++ tailWord_6921598) baseStart_6921598 baseEnd_6921598 := by
    simpa [prefixWord, tailWord_6921598, baseEnd_6921598] using wordTrace_append hprefix tailTrace_6921598
  have hstable : (prefixWord ++ tailWord_6921598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6921598).length < 2 ^ (prefixWord ++ tailWord_6921598).sum := by decide
  have hdescent : baseEnd_6921598 < baseStart_6921598 := by decide
  rcases family_descends (prefixWord ++ tailWord_6921598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6921663 : List Nat := [1, 1, 2, 2, 2, 1, 1, 3, 1, 6, 3]
def baseStart_6921663 : Nat := 118140960795 + 6921663 * 2 ^ 59
def prefixEnd_6921663 : Nat := 4983230072969 + 3 ^ 40 * 6921663 * 2
def baseEnd_6921663 : Nat := 3554140047441457695380357

theorem tailTrace_6921663 : CollatzResearch.WordTrace tailWord_6921663 prefixEnd_6921663 3554140047441457695380357 := by
  unfold tailWord_6921663
  simp only [CollatzResearch.WordTrace]
  refine ⟨252453789523004551771657643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168302526348669701181105095 252453789523004551771657643)
  ·
    refine ⟨378680684284506827657486465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252453789523004551771657643 378680684284506827657486465)
    ·
      refine ⟨284010513213380120743114849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 378680684284506827657486465 284010513213380120743114849)
      ·
        refine ⟨213007884910035090557336137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 284010513213380120743114849 213007884910035090557336137)
        ·
          refine ⟨159755913682526317918002103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213007884910035090557336137 159755913682526317918002103)
          ·
            refine ⟨239633870523789476877003155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159755913682526317918002103 239633870523789476877003155)
            ·
              refine ⟨359450805785684215315504733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239633870523789476877003155 359450805785684215315504733)
              ·
                refine ⟨134794052169631580743314275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 359450805785684215315504733 134794052169631580743314275)
                ·
                  refine ⟨202191078254447371114971413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134794052169631580743314275 202191078254447371114971413)
                  ·
                    refine ⟨9477706793177220521014285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 202191078254447371114971413 9477706793177220521014285)
                    ·
                      refine ⟨3554140047441457695380357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9477706793177220521014285 3554140047441457695380357)
                      ·
                        rfl

theorem cell23_6921663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 6, 3].length) (baseStart_6921663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6921663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6921663 prefixEnd_6921663 := by exact prefixLift 6921663
  have htrace : WordTrace (prefixWord ++ tailWord_6921663) baseStart_6921663 baseEnd_6921663 := by
    simpa [prefixWord, tailWord_6921663, baseEnd_6921663] using wordTrace_append hprefix tailTrace_6921663
  have hstable : (prefixWord ++ tailWord_6921663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6921663).length < 2 ^ (prefixWord ++ tailWord_6921663).sum := by decide
  have hdescent : baseEnd_6921663 < baseStart_6921663 := by decide
  rcases family_descends (prefixWord ++ tailWord_6921663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6921717 : List Nat := [1, 3, 5, 1, 1, 1, 3, 1, 7]
def baseStart_6921717 : Nat := 118140960795 + 6921717 * 2 ^ 59
def prefixEnd_6921717 : Nat := 4983230072969 + 3 ^ 40 * 6921717 * 2
def baseEnd_6921717 : Nat := 394907530599644498233901

theorem tailTrace_6921717 : CollatzResearch.WordTrace tailWord_6921717 prefixEnd_6921717 394907530599644498233901 := by
  unfold tailWord_6921717
  simp only [CollatzResearch.WordTrace]
  refine ⟨252455759064808918994123405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168303839376539279329415603 252455759064808918994123405)
  ·
    refine ⟨94670909649303344622796277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252455759064808918994123405 94670909649303344622796277)
    ·
      refine ⟨8875397779622188558387151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 94670909649303344622796277 8875397779622188558387151)
      ·
        refine ⟨13313096669433282837580727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8875397779622188558387151 13313096669433282837580727)
        ·
          refine ⟨19969645004149924256371091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13313096669433282837580727 19969645004149924256371091)
          ·
            refine ⟨29954467506224886384556637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19969645004149924256371091 29954467506224886384556637)
            ·
              refine ⟨11232925314834332394208739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29954467506224886384556637 11232925314834332394208739)
              ·
                refine ⟨16849387972251498591313109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11232925314834332394208739 16849387972251498591313109)
                ·
                  refine ⟨394907530599644498233901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16849387972251498591313109 394907530599644498233901)
                  ·
                    rfl

theorem cell23_6921717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 1, 7].length) (baseStart_6921717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6921717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6921717 prefixEnd_6921717 := by exact prefixLift 6921717
  have htrace : WordTrace (prefixWord ++ tailWord_6921717) baseStart_6921717 baseEnd_6921717 := by
    simpa [prefixWord, tailWord_6921717, baseEnd_6921717] using wordTrace_append hprefix tailTrace_6921717
  have hstable : (prefixWord ++ tailWord_6921717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6921717).length < 2 ^ (prefixWord ++ tailWord_6921717).sum := by decide
  have hdescent : baseEnd_6921717 < baseStart_6921717 := by decide
  rcases family_descends (prefixWord ++ tailWord_6921717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6921723 : List Nat := [1, 1, 1, 1, 1, 3, 2, 5, 1, 2, 5]
def baseStart_6921723 : Nat := 118140960795 + 6921723 * 2 ^ 59
def prefixEnd_6921723 : Nat := 4983230072969 + 3 ^ 40 * 6921723 * 2
def baseEnd_6921723 : Nat := 3554170856280727460630081

theorem tailTrace_6921723 : CollatzResearch.WordTrace tailWord_6921723 prefixEnd_6921723 3554170856280727460630081 := by
  unfold tailWord_6921723
  simp only [CollatzResearch.WordTrace]
  refine ⟨252455977902787182018841823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168303985268524788012561215 252455977902787182018841823)
  ·
    refine ⟨378683966854180773028262735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252455977902787182018841823 378683966854180773028262735)
    ·
      refine ⟨568025950281271159542394103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378683966854180773028262735 568025950281271159542394103)
      ·
        refine ⟨852038925421906739313591155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 568025950281271159542394103 852038925421906739313591155)
        ·
          refine ⟨1278058388132860108970386733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 852038925421906739313591155 1278058388132860108970386733)
          ·
            refine ⟨479271895549822540863895025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1278058388132860108970386733 479271895549822540863895025)
            ·
              refine ⟨359453921662366905647921269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 479271895549822540863895025 359453921662366905647921269)
              ·
                refine ⟨33698805155846897404492619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 359453921662366905647921269 33698805155846897404492619)
                ·
                  refine ⟨50548207733770346106738929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33698805155846897404492619 50548207733770346106738929)
                  ·
                    refine ⟨37911155800327759580054197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50548207733770346106738929 37911155800327759580054197)
                    ·
                      refine ⟨3554170856280727460630081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37911155800327759580054197 3554170856280727460630081)
                      ·
                        rfl

theorem cell23_6921723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 2, 5].length) (baseStart_6921723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6921723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6921723 prefixEnd_6921723 := by exact prefixLift 6921723
  have htrace : WordTrace (prefixWord ++ tailWord_6921723) baseStart_6921723 baseEnd_6921723 := by
    simpa [prefixWord, tailWord_6921723, baseEnd_6921723] using wordTrace_append hprefix tailTrace_6921723
  have hstable : (prefixWord ++ tailWord_6921723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6921723).length < 2 ^ (prefixWord ++ tailWord_6921723).sum := by decide
  have hdescent : baseEnd_6921723 < baseStart_6921723 := by decide
  rcases family_descends (prefixWord ++ tailWord_6921723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6921753 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 4, 3, 5]
def baseStart_6921753 : Nat := 118140960795 + 6921753 * 2 ^ 59
def prefixEnd_6921753 : Nat := 4983230072969 + 3 ^ 40 * 6921753 * 2
def baseEnd_6921753 : Nat := 3554186260700362343254943

theorem tailTrace_6921753 : CollatzResearch.WordTrace tailWord_6921753 prefixEnd_6921753 3554186260700362343254943 := by
  unfold tailWord_6921753
  simp only [CollatzResearch.WordTrace]
  refine ⟨252457072092678497142433913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168304714728452331428289275 252457072092678497142433913)
  ·
    refine ⟨189342804069508872856825435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252457072092678497142433913 189342804069508872856825435)
    ·
      refine ⟨284014206104263309285238153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189342804069508872856825435 284014206104263309285238153)
      ·
        refine ⟨213010654578197481963928615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 284014206104263309285238153 213010654578197481963928615)
        ·
          refine ⟨319515981867296222945892923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213010654578197481963928615 319515981867296222945892923)
          ·
            refine ⟨479273972800944334418839385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319515981867296222945892923 479273972800944334418839385)
            ·
              refine ⟨359455479600708250814129539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 479273972800944334418839385 359455479600708250814129539)
              ·
                refine ⟨539183219401062376221194309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 359455479600708250814129539 539183219401062376221194309)
                ·
                  refine ⟨101096853637699195541473933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 539183219401062376221194309 101096853637699195541473933)
                  ·
                    refine ⟨37911320114137198328052725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 101096853637699195541473933 37911320114137198328052725)
                    ·
                      refine ⟨3554186260700362343254943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37911320114137198328052725 3554186260700362343254943)
                      ·
                        rfl

theorem cell23_6921753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 3, 5].length) (baseStart_6921753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6921753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6921753 prefixEnd_6921753 := by exact prefixLift 6921753
  have htrace : WordTrace (prefixWord ++ tailWord_6921753) baseStart_6921753 baseEnd_6921753 := by
    simpa [prefixWord, tailWord_6921753, baseEnd_6921753] using wordTrace_append hprefix tailTrace_6921753
  have hstable : (prefixWord ++ tailWord_6921753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6921753).length < 2 ^ (prefixWord ++ tailWord_6921753).sum := by decide
  have hdescent : baseEnd_6921753 < baseStart_6921753 := by decide
  rcases family_descends (prefixWord ++ tailWord_6921753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6921768 : List Nat := [2, 1, 5, 2, 3, 1, 2, 2, 5]
def baseStart_6921768 : Nat := 118140960795 + 6921768 * 2 ^ 59
def prefixEnd_6921768 : Nat := 4983230072969 + 3 ^ 40 * 6921768 * 2
def baseEnd_6921768 : Nat := 394910440323353309396375

theorem tailTrace_6921768 : CollatzResearch.WordTrace tailWord_6921768 prefixEnd_6921768 394910440323353309396375 := by
  unfold tailWord_6921768
  simp only [CollatzResearch.WordTrace]
  refine ⟨126228809593812077352114979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168305079458416103136153305 126228809593812077352114979)
  ·
    refine ⟨189343214390718116028172469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126228809593812077352114979 189343214390718116028172469)
    ·
      refine ⟨17750926349129823377641169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 189343214390718116028172469 17750926349129823377641169)
      ·
        refine ⟨13313194761847367533230877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17750926349129823377641169 13313194761847367533230877)
        ·
          refine ⟨4992448035692762824961579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13313194761847367533230877 4992448035692762824961579)
          ·
            refine ⟨7488672053539144237442369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4992448035692762824961579 7488672053539144237442369)
            ·
              refine ⟨5616504040154358178081777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7488672053539144237442369 5616504040154358178081777)
              ·
                refine ⟨4212378030115768633561333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5616504040154358178081777 4212378030115768633561333)
                ·
                  refine ⟨394910440323353309396375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4212378030115768633561333 394910440323353309396375)
                  ·
                    rfl

theorem cell23_6921768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 2, 2, 5].length) (baseStart_6921768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6921768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6921768 prefixEnd_6921768 := by exact prefixLift 6921768
  have htrace : WordTrace (prefixWord ++ tailWord_6921768) baseStart_6921768 baseEnd_6921768 := by
    simpa [prefixWord, tailWord_6921768, baseEnd_6921768] using wordTrace_append hprefix tailTrace_6921768
  have hstable : (prefixWord ++ tailWord_6921768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6921768).length < 2 ^ (prefixWord ++ tailWord_6921768).sum := by decide
  have hdescent : baseEnd_6921768 < baseStart_6921768 := by decide
  rcases family_descends (prefixWord ++ tailWord_6921768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6921770 : List Nat := [3, 1, 4, 1, 1, 1, 1, 1, 2, 3, 5]
def baseStart_6921770 : Nat := 118140960795 + 6921770 * 2 ^ 59
def prefixEnd_6921770 : Nat := 4983230072969 + 3 ^ 40 * 6921770 * 2
def baseEnd_6921770 : Nat := 3554194989871488776742365

theorem tailTrace_6921770 : CollatzResearch.WordTrace tailWord_6921770 prefixEnd_6921770 3554194989871488776742365 := by
  unfold tailWord_6921770
  simp only [CollatzResearch.WordTrace]
  refine ⟨63114423033404227261450691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168305128089077939363868509 63114423033404227261450691)
  ·
    refine ⟨94671634550106340892176037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63114423033404227261450691 94671634550106340892176037)
    ·
      refine ⟨17750931478144938917283007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94671634550106340892176037 17750931478144938917283007)
      ·
        refine ⟨26626397217217408375924511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17750931478144938917283007 26626397217217408375924511)
        ·
          refine ⟨39939595825826112563886767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26626397217217408375924511 39939595825826112563886767)
          ·
            refine ⟨59909393738739168845830151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39939595825826112563886767 59909393738739168845830151)
            ·
              refine ⟨89864090608108753268745227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59909393738739168845830151 89864090608108753268745227)
              ·
                refine ⟨134796135912163129903117841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89864090608108753268745227 134796135912163129903117841)
                ·
                  refine ⟨101097101934122347427338381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134796135912163129903117841 101097101934122347427338381)
                  ·
                    refine ⟨37911413225295880285251893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 101097101934122347427338381 37911413225295880285251893)
                    ·
                      refine ⟨3554194989871488776742365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37911413225295880285251893 3554194989871488776742365)
                      ·
                        rfl

theorem cell23_6921770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_6921770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6921770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6921770 prefixEnd_6921770 := by exact prefixLift 6921770
  have htrace : WordTrace (prefixWord ++ tailWord_6921770) baseStart_6921770 baseEnd_6921770 := by
    simpa [prefixWord, tailWord_6921770, baseEnd_6921770] using wordTrace_append hprefix tailTrace_6921770
  have hstable : (prefixWord ++ tailWord_6921770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6921770).length < 2 ^ (prefixWord ++ tailWord_6921770).sum := by decide
  have hdescent : baseEnd_6921770 < baseStart_6921770 := by decide
  rcases family_descends (prefixWord ++ tailWord_6921770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6921798 : List Nat := [6, 1, 1, 1, 4, 1, 1, 1, 2, 5]
def baseStart_6921798 : Nat := 118140960795 + 6921798 * 2 ^ 59
def prefixEnd_6921798 : Nat := 4983230072969 + 3 ^ 40 * 6921798 * 2
def baseEnd_6921798 : Nat := 1184736455776604889064079

theorem tailTrace_6921798 : CollatzResearch.WordTrace tailWord_6921798 prefixEnd_6921798 1184736455776604889064079 := by
  unfold tailWord_6921798
  simp only [CollatzResearch.WordTrace]
  refine ⟨7889334793047358432119439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 168305808918343646551881365 7889334793047358432119439)
  ·
    refine ⟨11834002189571037648179159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7889334793047358432119439 11834002189571037648179159)
    ·
      refine ⟨17751003284356556472268739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11834002189571037648179159 17751003284356556472268739)
      ·
        refine ⟨26626504926534834708403109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17751003284356556472268739 26626504926534834708403109)
        ·
          refine ⟨4992469673725281507825583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26626504926534834708403109 4992469673725281507825583)
          ·
            refine ⟨7488704510587922261738375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4992469673725281507825583 7488704510587922261738375)
            ·
              refine ⟨11233056765881883392607563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7488704510587922261738375 11233056765881883392607563)
              ·
                refine ⟨16849585148822825088911345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11233056765881883392607563 16849585148822825088911345)
                ·
                  refine ⟨12637188861617118816683509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16849585148822825088911345 12637188861617118816683509)
                  ·
                    refine ⟨1184736455776604889064079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12637188861617118816683509 1184736455776604889064079)
                    ·
                      rfl

theorem cell23_6921798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_6921798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6921798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6921798 prefixEnd_6921798 := by exact prefixLift 6921798
  have htrace : WordTrace (prefixWord ++ tailWord_6921798) baseStart_6921798 baseEnd_6921798 := by
    simpa [prefixWord, tailWord_6921798, baseEnd_6921798] using wordTrace_append hprefix tailTrace_6921798
  have hstable : (prefixWord ++ tailWord_6921798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6921798).length < 2 ^ (prefixWord ++ tailWord_6921798).sum := by decide
  have hdescent : baseEnd_6921798 < baseStart_6921798 := by decide
  rcases family_descends (prefixWord ++ tailWord_6921798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6921804 : List Nat := [2, 2, 1, 3, 1, 5, 1, 1, 2, 2, 3]
def baseStart_6921804 : Nat := 118140960795 + 6921804 * 2 ^ 59
def prefixEnd_6921804 : Nat := 4983230072969 + 3 ^ 40 * 6921804 * 2
def baseEnd_6921804 : Nat := 3554212448213741643717209

theorem tailTrace_6921804 : CollatzResearch.WordTrace tailWord_6921804 prefixEnd_6921804 3554212448213741643717209 := by
  unfold tailWord_6921804
  simp only [CollatzResearch.WordTrace]
  refine ⟨126229466107746866426270233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168305954810329155235026977 126229466107746866426270233)
  ·
    refine ⟨94672099580810149819702675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126229466107746866426270233 94672099580810149819702675)
    ·
      refine ⟨142008149371215224729554013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94672099580810149819702675 142008149371215224729554013)
      ·
        refine ⟨53253056014205709273582755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142008149371215224729554013 53253056014205709273582755)
        ·
          refine ⟨79879584021308563910374133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53253056014205709273582755 79879584021308563910374133)
          ·
            refine ⟨7488711001997677866597575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79879584021308563910374133 7488711001997677866597575)
            ·
              refine ⟨11233066502996516799896363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7488711001997677866597575 11233066502996516799896363)
              ·
                refine ⟨16849599754494775199844545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11233066502996516799896363 16849599754494775199844545)
                ·
                  refine ⟨12637199815871081399883409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16849599754494775199844545 12637199815871081399883409)
                  ·
                    refine ⟨9477899861903311049912557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12637199815871081399883409 9477899861903311049912557)
                    ·
                      refine ⟨3554212448213741643717209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9477899861903311049912557 3554212448213741643717209)
                      ·
                        rfl

theorem cell23_6921804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 1, 2, 2, 3].length) (baseStart_6921804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6921804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6921804 prefixEnd_6921804 := by exact prefixLift 6921804
  have htrace : WordTrace (prefixWord ++ tailWord_6921804) baseStart_6921804 baseEnd_6921804 := by
    simpa [prefixWord, tailWord_6921804, baseEnd_6921804] using wordTrace_append hprefix tailTrace_6921804
  have hstable : (prefixWord ++ tailWord_6921804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6921804).length < 2 ^ (prefixWord ++ tailWord_6921804).sum := by decide
  have hdescent : baseEnd_6921804 < baseStart_6921804 := by decide
  rcases family_descends (prefixWord ++ tailWord_6921804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6921834 : List Nat := [3, 1, 3, 2, 1, 2, 1, 3, 3, 1, 3]
def baseStart_6921834 : Nat := 118140960795 + 6921834 * 2 ^ 59
def prefixEnd_6921834 : Nat := 4983230072969 + 3 ^ 40 * 6921834 * 2
def baseEnd_6921834 : Nat := 3554227852633376526342071

theorem tailTrace_6921834 : CollatzResearch.WordTrace tailWord_6921834 prefixEnd_6921834 3554227852633376526342071 := by
  unfold tailWord_6921834
  simp only [CollatzResearch.WordTrace]
  refine ⟨63115006601346261994033139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168306684270256698650755037 63115006601346261994033139)
  ·
    refine ⟨94672509902019392991049709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63115006601346261994033139 94672509902019392991049709)
    ·
      refine ⟨35502191213257272371643641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94672509902019392991049709 35502191213257272371643641)
      ·
        refine ⟨26626643409942954278732731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35502191213257272371643641 26626643409942954278732731)
        ·
          refine ⟨39939965114914431418099097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26626643409942954278732731 39939965114914431418099097)
          ·
            refine ⟨29954973836185823563574323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39939965114914431418099097 29954973836185823563574323)
            ·
              refine ⟨44932460754278735345361485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29954973836185823563574323 44932460754278735345361485)
              ·
                refine ⟨16849672782854525754510557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44932460754278735345361485 16849672782854525754510557)
                ·
                  refine ⟨6318627293570447157941459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16849672782854525754510557 6318627293570447157941459)
                  ·
                    refine ⟨9477940940355670736912189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6318627293570447157941459 9477940940355670736912189)
                    ·
                      refine ⟨3554227852633376526342071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9477940940355670736912189 3554227852633376526342071)
                      ·
                        rfl

theorem cell23_6921834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_6921834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6921834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6921834 prefixEnd_6921834 := by exact prefixLift 6921834
  have htrace : WordTrace (prefixWord ++ tailWord_6921834) baseStart_6921834 baseEnd_6921834 := by
    simpa [prefixWord, tailWord_6921834, baseEnd_6921834] using wordTrace_append hprefix tailTrace_6921834
  have hstable : (prefixWord ++ tailWord_6921834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6921834).length < 2 ^ (prefixWord ++ tailWord_6921834).sum := by decide
  have hdescent : baseEnd_6921834 < baseStart_6921834 := by decide
  rcases family_descends (prefixWord ++ tailWord_6921834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6921850 : List Nat := [3, 1, 1, 1, 1, 1, 1, 7, 1, 6]
def baseStart_6921850 : Nat := 118140960795 + 6921850 * 2 ^ 59
def prefixEnd_6921850 : Nat := 4983230072969 + 3 ^ 40 * 6921850 * 2
def baseEnd_6921850 : Nat := 1184745356107949487913999

theorem tailTrace_6921850 : CollatzResearch.WordTrace tailWord_6921850 prefixEnd_6921850 1184745356107949487913999 := by
  unfold tailWord_6921850
  simp only [CollatzResearch.WordTrace]
  refine ⟨63115152493331770677178751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168307073315551388472476669 63115152493331770677178751)
  ·
    refine ⟨94672728739997656015768127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63115152493331770677178751 94672728739997656015768127)
    ·
      refine ⟨142009093109996484023652191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94672728739997656015768127 142009093109996484023652191)
      ·
        refine ⟨213013639664994726035478287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142009093109996484023652191 213013639664994726035478287)
        ·
          refine ⟨319520459497492089053217431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213013639664994726035478287 319520459497492089053217431)
          ·
            refine ⟨479280689246238133579826147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319520459497492089053217431 479280689246238133579826147)
            ·
              refine ⟨718921033869357200369739221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 479280689246238133579826147 718921033869357200369739221)
              ·
                refine ⟨16849711731313059383665763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 718921033869357200369739221 16849711731313059383665763)
                ·
                  refine ⟨25274567596969589075498645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16849711731313059383665763 25274567596969589075498645)
                  ·
                    refine ⟨1184745356107949487913999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25274567596969589075498645 1184745356107949487913999)
                    ·
                      rfl

theorem cell23_6921850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 7, 1, 6].length) (baseStart_6921850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6921850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6921850 prefixEnd_6921850 := by exact prefixLift 6921850
  have htrace : WordTrace (prefixWord ++ tailWord_6921850) baseStart_6921850 baseEnd_6921850 := by
    simpa [prefixWord, tailWord_6921850, baseEnd_6921850] using wordTrace_append hprefix tailTrace_6921850
  have hstable : (prefixWord ++ tailWord_6921850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6921850).length < 2 ^ (prefixWord ++ tailWord_6921850).sum := by decide
  have hdescent : baseEnd_6921850 < baseStart_6921850 := by decide
  rcases family_descends (prefixWord ++ tailWord_6921850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6921880 : List Nat := [2, 1, 2, 4, 1, 2, 11]
def baseStart_6921880 : Nat := 118140960795 + 6921880 * 2 ^ 59
def prefixEnd_6921880 : Nat := 4983230072969 + 3 ^ 40 * 6921880 * 2
def baseEnd_6921880 : Nat := 43879647811647942547739

theorem tailTrace_6921880 : CollatzResearch.WordTrace tailWord_6921880 prefixEnd_6921880 43879647811647942547739 := by
  unfold tailWord_6921880
  simp only [CollatzResearch.WordTrace]
  refine ⟨126230852081609198916153547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168307802775478931888204729 126230852081609198916153547)
  ·
    refine ⟨189346278122413798374230321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126230852081609198916153547 189346278122413798374230321)
    ·
      refine ⟨142009708591810348780672741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189346278122413798374230321 142009708591810348780672741)
      ·
        refine ⟨26626820360964440396376139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142009708591810348780672741 26626820360964440396376139)
        ·
          refine ⟨39940230541446660594564209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26626820360964440396376139 39940230541446660594564209)
          ·
            refine ⟨29955172906084995445923157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39940230541446660594564209 29955172906084995445923157)
            ·
              refine ⟨43879647811647942547739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 29955172906084995445923157 43879647811647942547739)
              ·
                rfl

theorem cell23_6921880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 11].length) (baseStart_6921880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6921880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6921880 prefixEnd_6921880 := by exact prefixLift 6921880
  have htrace : WordTrace (prefixWord ++ tailWord_6921880) baseStart_6921880 baseEnd_6921880 := by
    simpa [prefixWord, tailWord_6921880, baseEnd_6921880] using wordTrace_append hprefix tailTrace_6921880
  have hstable : (prefixWord ++ tailWord_6921880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6921880).length < 2 ^ (prefixWord ++ tailWord_6921880).sum := by decide
  have hdescent : baseEnd_6921880 < baseStart_6921880 := by decide
  rcases family_descends (prefixWord ++ tailWord_6921880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6921907 : List Nat := [1, 1, 1, 2, 3, 3, 2, 3, 1, 3, 3]
def baseStart_6921907 : Nat := 118140960795 + 6921907 * 2 ^ 59
def prefixEnd_6921907 : Nat := 4983230072969 + 3 ^ 40 * 6921907 * 2
def baseEnd_6921907 : Nat := 3554265336721154740729235

theorem tailTrace_6921907 : CollatzResearch.WordTrace tailWord_6921907 prefixEnd_6921907 3554265336721154740729235 := by
  unfold tailWord_6921907
  simp only [CollatzResearch.WordTrace]
  refine ⟨252462688934120581443539975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168308459289413720962359983 252462688934120581443539975)
  ·
    refine ⟨378694033401180872165309963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252462688934120581443539975 378694033401180872165309963)
    ·
      refine ⟨568041050101771308247964945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378694033401180872165309963 568041050101771308247964945)
      ·
        refine ⟨426030787576328481185973709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 568041050101771308247964945 426030787576328481185973709)
        ·
          refine ⟨159761545341123180444740141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 426030787576328481185973709 159761545341123180444740141)
          ·
            refine ⟨59910579502921192666777553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159761545341123180444740141 59910579502921192666777553)
            ·
              refine ⟨44932934627190894500083165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59910579502921192666777553 44932934627190894500083165)
              ·
                refine ⟨16849850485196585437531187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44932934627190894500083165 16849850485196585437531187)
                ·
                  refine ⟨25274775727794878156296781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16849850485196585437531187 25274775727794878156296781)
                  ·
                    refine ⟨9478040897923079308611293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25274775727794878156296781 9478040897923079308611293)
                    ·
                      refine ⟨3554265336721154740729235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9478040897923079308611293 3554265336721154740729235)
                      ·
                        rfl

theorem cell23_6921907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 3, 1, 3, 3].length) (baseStart_6921907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6921907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6921907 prefixEnd_6921907 := by exact prefixLift 6921907
  have htrace : WordTrace (prefixWord ++ tailWord_6921907) baseStart_6921907 baseEnd_6921907 := by
    simpa [prefixWord, tailWord_6921907, baseEnd_6921907] using wordTrace_append hprefix tailTrace_6921907
  have hstable : (prefixWord ++ tailWord_6921907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6921907).length < 2 ^ (prefixWord ++ tailWord_6921907).sum := by decide
  have hdescent : baseEnd_6921907 < baseStart_6921907 := by decide
  rcases family_descends (prefixWord ++ tailWord_6921907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6921911 : List Nat := [1, 1, 3, 1, 5, 3, 1, 2, 1, 2, 3]
def baseStart_6921911 : Nat := 118140960795 + 6921911 * 2 ^ 59
def prefixEnd_6921911 : Nat := 4983230072969 + 3 ^ 40 * 6921911 * 2
def baseEnd_6921911 : Nat := 3554267390643772725079217

theorem tailTrace_6921911 : CollatzResearch.WordTrace tailWord_6921911 prefixEnd_6921911 3554267390643772725079217 := by
  unfold tailWord_6921911
  simp only [CollatzResearch.WordTrace]
  refine ⟨252462834826106090126685587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168308556550737393417790391 252462834826106090126685587)
  ·
    refine ⟨378694252239159135190028381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252462834826106090126685587 378694252239159135190028381)
    ·
      refine ⟨142010344589684675696260643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 378694252239159135190028381 142010344589684675696260643)
      ·
        refine ⟨213015516884527013544390965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142010344589684675696260643 213015516884527013544390965)
        ·
          refine ⟨19970204707924407519786653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 213015516884527013544390965 19970204707924407519786653)
          ·
            refine ⟨7488826765471652819919995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19970204707924407519786653 7488826765471652819919995)
            ·
              refine ⟨11233240148207479229879993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7488826765471652819919995 11233240148207479229879993)
              ·
                refine ⟨8424930111155609422409995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11233240148207479229879993 8424930111155609422409995)
                ·
                  refine ⟨12637395166733414133614993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8424930111155609422409995 12637395166733414133614993)
                  ·
                    refine ⟨9478046375050060600211245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12637395166733414133614993 9478046375050060600211245)
                    ·
                      refine ⟨3554267390643772725079217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9478046375050060600211245 3554267390643772725079217)
                      ·
                        rfl

theorem cell23_6921911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 2, 1, 2, 3].length) (baseStart_6921911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6921911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6921911 prefixEnd_6921911 := by exact prefixLift 6921911
  have htrace : WordTrace (prefixWord ++ tailWord_6921911) baseStart_6921911 baseEnd_6921911 := by
    simpa [prefixWord, tailWord_6921911, baseEnd_6921911] using wordTrace_append hprefix tailTrace_6921911
  have hstable : (prefixWord ++ tailWord_6921911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6921911).length < 2 ^ (prefixWord ++ tailWord_6921911).sum := by decide
  have hdescent : baseEnd_6921911 < baseStart_6921911 := by decide
  rcases family_descends (prefixWord ++ tailWord_6921911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6921924 : List Nat := [2, 3, 3, 1, 1, 1, 3, 2, 1, 3, 3]
def baseStart_6921924 : Nat := 118140960795 + 6921924 * 2 ^ 59
def prefixEnd_6921924 : Nat := 4983230072969 + 3 ^ 40 * 6921924 * 2
def baseEnd_6921924 : Nat := 3554274065892281174216657

theorem tailTrace_6921924 : CollatzResearch.WordTrace tailWord_6921924 prefixEnd_6921924 3554274065892281174216657 := by
  unfold tailWord_6921924
  simp only [CollatzResearch.WordTrace]
  refine ⟨126231654487529496673454413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168308872650039328897939217 126231654487529496673454413)
  ·
    refine ⟨47336870432823561252545405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126231654487529496673454413 47336870432823561252545405)
    ·
      refine ⟨17751326412308835469704527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47336870432823561252545405 17751326412308835469704527)
      ·
        refine ⟨26626989618463253204556791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17751326412308835469704527 26626989618463253204556791)
        ·
          refine ⟨39940484427694879806835187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26626989618463253204556791 39940484427694879806835187)
          ·
            refine ⟨59910726641542319710252781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39940484427694879806835187 59910726641542319710252781)
            ·
              refine ⟨22466522490578369891344793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59910726641542319710252781 22466522490578369891344793)
              ·
                refine ⟨16849891867933777418508595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22466522490578369891344793 16849891867933777418508595)
                ·
                  refine ⟨25274837801900666127762893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16849891867933777418508595 25274837801900666127762893)
                  ·
                    refine ⟨9478064175712749797911085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25274837801900666127762893 9478064175712749797911085)
                    ·
                      refine ⟨3554274065892281174216657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9478064175712749797911085 3554274065892281174216657)
                      ·
                        rfl

theorem cell23_6921924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_6921924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6921924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6921924 prefixEnd_6921924 := by exact prefixLift 6921924
  have htrace : WordTrace (prefixWord ++ tailWord_6921924) baseStart_6921924 baseEnd_6921924 := by
    simpa [prefixWord, tailWord_6921924, baseEnd_6921924] using wordTrace_append hprefix tailTrace_6921924
  have hstable : (prefixWord ++ tailWord_6921924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6921924).length < 2 ^ (prefixWord ++ tailWord_6921924).sum := by decide
  have hdescent : baseEnd_6921924 < baseStart_6921924 := by decide
  rcases family_descends (prefixWord ++ tailWord_6921924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6921947 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 1, 10, 2]
def baseStart_6921947 : Nat := 118140960795 + 6921947 * 2 ^ 59
def prefixEnd_6921947 : Nat := 4983230072969 + 3 ^ 40 * 6921947 * 2
def baseEnd_6921947 : Nat := 3554285875947334584229051

theorem tailTrace_6921947 : CollatzResearch.WordTrace tailWord_6921947 prefixEnd_6921947 3554285875947334584229051 := by
  unfold tailWord_6921947
  simp only [CollatzResearch.WordTrace]
  refine ⟨252464147853975668274996095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168309431902650445516664063 252464147853975668274996095)
  ·
    refine ⟨378696221780963502412494143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252464147853975668274996095 378696221780963502412494143)
    ·
      refine ⟨568044332671445253618741215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378696221780963502412494143 568044332671445253618741215)
      ·
        refine ⟨852066499007167880428111823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 568044332671445253618741215 852066499007167880428111823)
        ·
          refine ⟨1278099748510751820642167735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 852066499007167880428111823 1278099748510751820642167735)
          ·
            refine ⟨1917149622766127730963251603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1278099748510751820642167735 1917149622766127730963251603)
            ·
              refine ⟨2875724434149191596444877405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1917149622766127730963251603 2875724434149191596444877405)
              ·
                refine ⟨1078396662805946848666829027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2875724434149191596444877405 1078396662805946848666829027)
                ·
                  refine ⟨1617594994208920273000243541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1078396662805946848666829027 1617594994208920273000243541)
                  ·
                    refine ⟨4739047834596446112305401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 1617594994208920273000243541 4739047834596446112305401)
                    ·
                      refine ⟨3554285875947334584229051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4739047834596446112305401 3554285875947334584229051)
                      ·
                        rfl

theorem cell23_6921947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 10, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 10, 2].length) (baseStart_6921947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6921947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6921947 prefixEnd_6921947 := by exact prefixLift 6921947
  have htrace : WordTrace (prefixWord ++ tailWord_6921947) baseStart_6921947 baseEnd_6921947 := by
    simpa [prefixWord, tailWord_6921947, baseEnd_6921947] using wordTrace_append hprefix tailTrace_6921947
  have hstable : (prefixWord ++ tailWord_6921947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6921947).length < 2 ^ (prefixWord ++ tailWord_6921947).sum := by decide
  have hdescent : baseEnd_6921947 < baseStart_6921947 := by decide
  rcases family_descends (prefixWord ++ tailWord_6921947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6921957 : List Nat := [1, 3, 1, 4, 1, 1, 3, 1, 2, 6]
def baseStart_6921957 : Nat := 118140960795 + 6921957 * 2 ^ 59
def prefixEnd_6921957 : Nat := 4983230072969 + 3 ^ 40 * 6921957 * 2
def baseEnd_6921957 : Nat := 1184763670251293181701335

theorem tailTrace_6921957 : CollatzResearch.WordTrace tailWord_6921957 prefixEnd_6921957 1184763670251293181701335 := by
  unfold tailWord_6921957
  simp only [CollatzResearch.WordTrace]
  refine ⟨252464512583939439982860125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168309675055959626655240083 252464512583939439982860125)
  ·
    refine ⟨94674192218977289993572547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252464512583939439982860125 94674192218977289993572547)
    ·
      refine ⟨142011288328465934990358821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94674192218977289993572547 142011288328465934990358821)
      ·
        refine ⟨26627116561587362810692279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142011288328465934990358821 26627116561587362810692279)
        ·
          refine ⟨39940674842381044216038419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26627116561587362810692279 39940674842381044216038419)
          ·
            refine ⟨59911012263571566324057629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39940674842381044216038419 59911012263571566324057629)
            ·
              refine ⟨22466629598839337371521611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59911012263571566324057629 22466629598839337371521611)
              ·
                refine ⟨33699944398259006057282417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22466629598839337371521611 33699944398259006057282417)
                ·
                  refine ⟨25274958298694254542961813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33699944398259006057282417 25274958298694254542961813)
                  ·
                    refine ⟨1184763670251293181701335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25274958298694254542961813 1184763670251293181701335)
                    ·
                      rfl

theorem cell23_6921957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 2, 6].length) (baseStart_6921957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6921957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6921957 prefixEnd_6921957 := by exact prefixLift 6921957
  have htrace : WordTrace (prefixWord ++ tailWord_6921957) baseStart_6921957 baseEnd_6921957 := by
    simpa [prefixWord, tailWord_6921957, baseEnd_6921957] using wordTrace_append hprefix tailTrace_6921957
  have hstable : (prefixWord ++ tailWord_6921957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6921957).length < 2 ^ (prefixWord ++ tailWord_6921957).sum := by decide
  have hdescent : baseEnd_6921957 < baseStart_6921957 := by decide
  rcases family_descends (prefixWord ++ tailWord_6921957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6921964 : List Nat := [2, 2, 1, 1, 2, 2, 3, 3, 1, 4, 2]
def baseStart_6921964 : Nat := 118140960795 + 6921964 * 2 ^ 59
def prefixEnd_6921964 : Nat := 4983230072969 + 3 ^ 40 * 6921964 * 2
def baseEnd_6921964 : Nat := 3554294605118461017716473

theorem tailTrace_6921964 : CollatzResearch.WordTrace tailWord_6921964 prefixEnd_6921964 3554294605118461017716473 := by
  unfold tailWord_6921964
  simp only [CollatzResearch.WordTrace]
  refine ⟨126232383947457040089182473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168309845263276053452243297 126232383947457040089182473)
  ·
    refine ⟨94674287960592780066886855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126232383947457040089182473 94674287960592780066886855)
    ·
      refine ⟨142011431940889170100330283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94674287960592780066886855 142011431940889170100330283)
      ·
        refine ⟨213017147911333755150495425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142011431940889170100330283 213017147911333755150495425)
        ·
          refine ⟨159762860933500316362871569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213017147911333755150495425 159762860933500316362871569)
          ·
            refine ⟨119822145700125237272153677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159762860933500316362871569 119822145700125237272153677)
            ·
              refine ⟨44933304637546963977057629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119822145700125237272153677 44933304637546963977057629)
              ·
                refine ⟨16849989239080111491396611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44933304637546963977057629 16849989239080111491396611)
                ·
                  refine ⟨25274983858620167237094917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16849989239080111491396611 25274983858620167237094917)
                  ·
                    refine ⟨4739059473491281356955297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25274983858620167237094917 4739059473491281356955297)
                    ·
                      refine ⟨3554294605118461017716473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4739059473491281356955297 3554294605118461017716473)
                      ·
                        rfl

theorem cell23_6921964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 4, 2].length) (baseStart_6921964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6921964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6921964 prefixEnd_6921964 := by exact prefixLift 6921964
  have htrace : WordTrace (prefixWord ++ tailWord_6921964) baseStart_6921964 baseEnd_6921964 := by
    simpa [prefixWord, tailWord_6921964, baseEnd_6921964] using wordTrace_append hprefix tailTrace_6921964
  have hstable : (prefixWord ++ tailWord_6921964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6921964).length < 2 ^ (prefixWord ++ tailWord_6921964).sum := by decide
  have hdescent : baseEnd_6921964 < baseStart_6921964 := by decide
  rcases family_descends (prefixWord ++ tailWord_6921964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6921967 : List Nat := [1, 1, 2, 1, 5, 1, 1, 2, 2, 4, 3]
def baseStart_6921967 : Nat := 118140960795 + 6921967 * 2 ^ 59
def prefixEnd_6921967 : Nat := 4983230072969 + 3 ^ 40 * 6921967 * 2
def baseEnd_6921967 : Nat := 3554296145560424505978959

theorem tailTrace_6921967 : CollatzResearch.WordTrace tailWord_6921967 prefixEnd_6921967 3554296145560424505978959 := by
  unfold tailWord_6921967
  simp only [CollatzResearch.WordTrace]
  refine ⟨252464877313903211690724155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168309918209268807793816103 252464877313903211690724155)
  ·
    refine ⟨378697315970854817536086233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252464877313903211690724155 378697315970854817536086233)
    ·
      refine ⟨284022986978141113152064675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 378697315970854817536086233 284022986978141113152064675)
      ·
        refine ⟨426034480467211669728097013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284022986978141113152064675 426034480467211669728097013)
        ·
          refine ⟨39940732543801094037009095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 426034480467211669728097013 39940732543801094037009095)
          ·
            refine ⟨59911098815701641055513643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39940732543801094037009095 59911098815701641055513643)
            ·
              refine ⟨89866648223552461583270465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59911098815701641055513643 89866648223552461583270465)
              ·
                refine ⟨67399986167664346187452849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89866648223552461583270465 67399986167664346187452849)
                ·
                  refine ⟨50549989625748259640589637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67399986167664346187452849 50549989625748259640589637)
                  ·
                    refine ⟨9478123054827798682610557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50549989625748259640589637 9478123054827798682610557)
                    ·
                      refine ⟨3554296145560424505978959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9478123054827798682610557 3554296145560424505978959)
                      ·
                        rfl

theorem cell23_6921967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 4, 3].length) (baseStart_6921967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6921967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6921967 prefixEnd_6921967 := by exact prefixLift 6921967
  have htrace : WordTrace (prefixWord ++ tailWord_6921967) baseStart_6921967 baseEnd_6921967 := by
    simpa [prefixWord, tailWord_6921967, baseEnd_6921967] using wordTrace_append hprefix tailTrace_6921967
  have hstable : (prefixWord ++ tailWord_6921967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6921967).length < 2 ^ (prefixWord ++ tailWord_6921967).sum := by decide
  have hdescent : baseEnd_6921967 < baseStart_6921967 := by decide
  rcases family_descends (prefixWord ++ tailWord_6921967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6921998 : List Nat := [4, 1, 1, 2, 1, 1, 5, 2, 2, 2, 2]
def baseStart_6921998 : Nat := 118140960795 + 6921998 * 2 ^ 59
def prefixEnd_6921998 : Nat := 4983230072969 + 3 ^ 40 * 6921998 * 2
def baseEnd_6921998 : Nat := 3554312063460713884691317

theorem tailTrace_6921998 : CollatzResearch.WordTrace tailWord_6921998 prefixEnd_6921998 3554312063460713884691317 := by
  unfold tailWord_6921998
  simp only [CollatzResearch.WordTrace]
  refine ⟨31558250997098862998137831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168310671984527269323401765 31558250997098862998137831)
  ·
    refine ⟨47337376495648294497206747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31558250997098862998137831 47337376495648294497206747)
    ·
      refine ⟨71006064743472441745810121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47337376495648294497206747 71006064743472441745810121)
      ·
        refine ⟨53254548557604331309357591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71006064743472441745810121 53254548557604331309357591)
        ·
          refine ⟨79881822836406496964036387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53254548557604331309357591 79881822836406496964036387)
          ·
            refine ⟨119822734254609745446054581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79881822836406496964036387 119822734254609745446054581)
            ·
              refine ⟨11233381336369663635567617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 119822734254609745446054581 11233381336369663635567617)
              ·
                refine ⟨8425036002277247726675713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11233381336369663635567617 8425036002277247726675713)
                ·
                  refine ⟨6318777001707935795006785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8425036002277247726675713 6318777001707935795006785)
                  ·
                    refine ⟨4739082751280951846255089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6318777001707935795006785 4739082751280951846255089)
                    ·
                      refine ⟨3554312063460713884691317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4739082751280951846255089 3554312063460713884691317)
                      ·
                        rfl

theorem cell23_6921998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 2, 2, 2, 2].length) (baseStart_6921998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6921998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6921998 prefixEnd_6921998 := by exact prefixLift 6921998
  have htrace : WordTrace (prefixWord ++ tailWord_6921998) baseStart_6921998 baseEnd_6921998 := by
    simpa [prefixWord, tailWord_6921998, baseEnd_6921998] using wordTrace_append hprefix tailTrace_6921998
  have hstable : (prefixWord ++ tailWord_6921998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6921998).length < 2 ^ (prefixWord ++ tailWord_6921998).sum := by decide
  have hdescent : baseEnd_6921998 < baseStart_6921998 := by decide
  rcases family_descends (prefixWord ++ tailWord_6921998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6922017 : List Nat := [1, 2, 3, 2, 1, 3, 1, 2, 1, 7]
def baseStart_6922017 : Nat := 118140960795 + 6922017 * 2 ^ 59
def prefixEnd_6922017 : Nat := 4983230072969 + 3 ^ 40 * 6922017 * 2
def baseEnd_6922017 : Nat := 1184773939864383103451243

theorem tailTrace_6922017 : CollatzResearch.WordTrace tailWord_6922017 prefixEnd_6922017 1184773939864383103451243 := by
  unfold tailWord_6922017
  simp only [CollatzResearch.WordTrace]
  refine ⟨252466700963722070230044305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168311133975814713486696203 252466700963722070230044305)
  ·
    refine ⟨189350025722791552672533229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252466700963722070230044305 189350025722791552672533229)
    ·
      refine ⟨71006259646046832252199961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189350025722791552672533229 71006259646046832252199961)
      ·
        refine ⟨53254694734535124189149971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71006259646046832252199961 53254694734535124189149971)
        ·
          refine ⟨79882042101802686283724957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53254694734535124189149971 79882042101802686283724957)
          ·
            refine ⟨29955765788176007356396859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79882042101802686283724957 29955765788176007356396859)
            ·
              refine ⟨44933648682264011034595289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29955765788176007356396859 44933648682264011034595289)
              ·
                refine ⟨33700236511698008275946467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44933648682264011034595289 33700236511698008275946467)
                ·
                  refine ⟨50550354767547012413919701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33700236511698008275946467 50550354767547012413919701)
                  ·
                    refine ⟨1184773939864383103451243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50550354767547012413919701 1184773939864383103451243)
                    ·
                      rfl

theorem cell23_6922017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 7].length) (baseStart_6922017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6922017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6922017 prefixEnd_6922017 := by exact prefixLift 6922017
  have htrace : WordTrace (prefixWord ++ tailWord_6922017) baseStart_6922017 baseEnd_6922017 := by
    simpa [prefixWord, tailWord_6922017, baseEnd_6922017] using wordTrace_append hprefix tailTrace_6922017
  have hstable : (prefixWord ++ tailWord_6922017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6922017).length < 2 ^ (prefixWord ++ tailWord_6922017).sum := by decide
  have hdescent : baseEnd_6922017 < baseStart_6922017 := by decide
  rcases family_descends (prefixWord ++ tailWord_6922017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6922038 : List Nat := [5, 1, 2, 2, 1, 1, 3, 3, 5]
def baseStart_6922038 : Nat := 118140960795 + 6922038 * 2 ^ 59
def prefixEnd_6922038 : Nat := 4983230072969 + 3 ^ 40 * 6922038 * 2
def baseEnd_6922038 : Nat := 394925844742988192021237

theorem tailTrace_6922038 : CollatzResearch.WordTrace tailWord_6922038 prefixEnd_6922038 394925844742988192021237 := by
  unfold tailWord_6922038
  simp only [CollatzResearch.WordTrace]
  refine ⟨15779216681040374426034923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 168311644597763993877705845 15779216681040374426034923)
  ·
    refine ⟨23668825021560561639052385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15779216681040374426034923 23668825021560561639052385)
    ·
      refine ⟨17751618766170421229289289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23668825021560561639052385 17751618766170421229289289)
      ·
        refine ⟨13313714074627815921966967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17751618766170421229289289 13313714074627815921966967)
        ·
          refine ⟨19970571111941723882950451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13313714074627815921966967 19970571111941723882950451)
          ·
            refine ⟨29955856667912585824425677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19970571111941723882950451 29955856667912585824425677)
            ·
              refine ⟨11233446250467219684159629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29955856667912585824425677 11233446250467219684159629)
              ·
                refine ⟨4212542343925207381559861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11233446250467219684159629 4212542343925207381559861)
                ·
                  refine ⟨394925844742988192021237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4212542343925207381559861 394925844742988192021237)
                  ·
                    rfl

theorem cell23_6922038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 3, 5].length) (baseStart_6922038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6922038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6922038 prefixEnd_6922038 := by exact prefixLift 6922038
  have htrace : WordTrace (prefixWord ++ tailWord_6922038) baseStart_6922038 baseEnd_6922038 := by
    simpa [prefixWord, tailWord_6922038, baseEnd_6922038] using wordTrace_append hprefix tailTrace_6922038
  have hstable : (prefixWord ++ tailWord_6922038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6922038).length < 2 ^ (prefixWord ++ tailWord_6922038).sum := by decide
  have hdescent : baseEnd_6922038 < baseStart_6922038 := by decide
  rcases family_descends (prefixWord ++ tailWord_6922038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6922061 : List Nat := [1, 6, 1, 2, 1, 2, 1, 1, 1, 2, 5]
def baseStart_6922061 : Nat := 118140960795 + 6922061 * 2 ^ 59
def prefixEnd_6922061 : Nat := 4983230072969 + 3 ^ 40 * 6922061 * 2
def baseEnd_6922061 : Nat := 3554344412741947138203527

theorem tailTrace_6922061 : CollatzResearch.WordTrace tailWord_6922061 prefixEnd_6922061 3554344412741947138203527 := by
  unfold tailWord_6922061
  simp only [CollatzResearch.WordTrace]
  refine ⟨252468305775562665744646037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168312203850375110496430691 252468305775562665744646037)
  ·
    refine ⟨11834451833229499956780283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 252468305775562665744646037 11834451833229499956780283)
    ·
      refine ⟨17751677749844249935170425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11834451833229499956780283 17751677749844249935170425)
      ·
        refine ⟨13313758312383187451377819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17751677749844249935170425 13313758312383187451377819)
        ·
          refine ⟨19970637468574781177066729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13313758312383187451377819 19970637468574781177066729)
          ·
            refine ⟨14977978101431085882800047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19970637468574781177066729 14977978101431085882800047)
            ·
              refine ⟨22466967152146628824200071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14977978101431085882800047 22466967152146628824200071)
              ·
                refine ⟨33700450728219943236300107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22466967152146628824200071 33700450728219943236300107)
                ·
                  refine ⟨50550676092329914854450161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33700450728219943236300107 50550676092329914854450161)
                  ·
                    refine ⟨37913007069247436140837621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50550676092329914854450161 37913007069247436140837621)
                    ·
                      refine ⟨3554344412741947138203527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37913007069247436140837621 3554344412741947138203527)
                      ·
                        rfl

theorem cell23_6922061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_6922061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6922061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6922061 prefixEnd_6922061 := by exact prefixLift 6922061
  have htrace : WordTrace (prefixWord ++ tailWord_6922061) baseStart_6922061 baseEnd_6922061 := by
    simpa [prefixWord, tailWord_6922061, baseEnd_6922061] using wordTrace_append hprefix tailTrace_6922061
  have hstable : (prefixWord ++ tailWord_6922061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6922061).length < 2 ^ (prefixWord ++ tailWord_6922061).sum := by decide
  have hdescent : baseEnd_6922061 < baseStart_6922061 := by decide
  rcases family_descends (prefixWord ++ tailWord_6922061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6922074 : List Nat := [3, 1, 1, 2, 1, 3, 1, 2, 4, 2, 3]
def baseStart_6922074 : Nat := 118140960795 + 6922074 * 2 ^ 59
def prefixEnd_6922074 : Nat := 4983230072969 + 3 ^ 40 * 6922074 * 2
def baseEnd_6922074 : Nat := 3554351087990455587340967

theorem tailTrace_6922074 : CollatzResearch.WordTrace tailWord_6922074 prefixEnd_6922074 3554351087990455587340967 := by
  unfold tailWord_6922074
  simp only [CollatzResearch.WordTrace]
  refine ⟨63117194981128892241217319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168312519949677045976579517 63117194981128892241217319)
  ·
    refine ⟨94675792471693338361825979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63117194981128892241217319 94675792471693338361825979)
    ·
      refine ⟨142013688707540007542738969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94675792471693338361825979 142013688707540007542738969)
      ·
        refine ⟨106510266530655005657054227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142013688707540007542738969 106510266530655005657054227)
        ·
          refine ⟨159765399795982508485581341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106510266530655005657054227 159765399795982508485581341)
          ·
            refine ⟨59912024923493440682093003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159765399795982508485581341 59912024923493440682093003)
            ·
              refine ⟨89868037385240161023139505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59912024923493440682093003 89868037385240161023139505)
              ·
                refine ⟨67401028038930120767354629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89868037385240161023139505 67401028038930120767354629)
                ·
                  refine ⟨12637692757299397643878993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67401028038930120767354629 12637692757299397643878993)
                  ·
                    refine ⟨9478269567974548232909245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12637692757299397643878993 9478269567974548232909245)
                    ·
                      refine ⟨3554351087990455587340967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9478269567974548232909245 3554351087990455587340967)
                      ·
                        rfl

theorem cell23_6922074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 4, 2, 3].length) (baseStart_6922074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6922074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6922074 prefixEnd_6922074 := by exact prefixLift 6922074
  have htrace : WordTrace (prefixWord ++ tailWord_6922074) baseStart_6922074 baseEnd_6922074 := by
    simpa [prefixWord, tailWord_6922074, baseEnd_6922074] using wordTrace_append hprefix tailTrace_6922074
  have hstable : (prefixWord ++ tailWord_6922074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6922074).length < 2 ^ (prefixWord ++ tailWord_6922074).sum := by decide
  have hdescent : baseEnd_6922074 < baseStart_6922074 := by decide
  rcases family_descends (prefixWord ++ tailWord_6922074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6922115 : List Nat := [1, 1, 1, 3, 4, 4, 2, 2, 1, 4]
def baseStart_6922115 : Nat := 118140960795 + 6922115 * 2 ^ 59
def prefixEnd_6922115 : Nat := 4983230072969 + 3 ^ 40 * 6922115 * 2
def baseEnd_6922115 : Nat := 1184790713565763308976093

theorem tailTrace_6922115 : CollatzResearch.WordTrace tailWord_6922115 prefixEnd_6922115 1184790713565763308976093 := by
  unfold tailWord_6922115
  simp only [CollatzResearch.WordTrace]
  refine ⟨252470275317367032967111799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168313516878244688644741199 252470275317367032967111799)
  ·
    refine ⟨378705412976050549450667699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252470275317367032967111799 378705412976050549450667699)
    ·
      refine ⟨568058119464075824176001549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378705412976050549450667699 568058119464075824176001549)
      ·
        refine ⟨213021794799028434066000581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 568058119464075824176001549 213021794799028434066000581)
        ·
          refine ⟨39941586524817831387375109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 213021794799028434066000581 39941586524817831387375109)
          ·
            refine ⟨7489047473403343385132833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39941586524817831387375109 7489047473403343385132833)
            ·
              refine ⟨5616785605052507538849625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7489047473403343385132833 5616785605052507538849625)
              ·
                refine ⟨4212589203789380654137219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5616785605052507538849625 4212589203789380654137219)
                ·
                  refine ⟨6318883805684070981205829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4212589203789380654137219 6318883805684070981205829)
                  ·
                    refine ⟨1184790713565763308976093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6318883805684070981205829 1184790713565763308976093)
                    ·
                      rfl

theorem cell23_6922115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 2, 2, 1, 4].length) (baseStart_6922115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6922115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6922115 prefixEnd_6922115 := by exact prefixLift 6922115
  have htrace : WordTrace (prefixWord ++ tailWord_6922115) baseStart_6922115 baseEnd_6922115 := by
    simpa [prefixWord, tailWord_6922115, baseEnd_6922115] using wordTrace_append hprefix tailTrace_6922115
  have hstable : (prefixWord ++ tailWord_6922115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6922115).length < 2 ^ (prefixWord ++ tailWord_6922115).sum := by decide
  have hdescent : baseEnd_6922115 < baseStart_6922115 := by decide
  rcases family_descends (prefixWord ++ tailWord_6922115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6922121 : List Nat := [1, 2, 1, 1, 5, 1, 2, 3, 3, 1, 3]
def baseStart_6922121 : Nat := 118140960795 + 6922121 * 2 ^ 59
def prefixEnd_6922121 : Nat := 4983230072969 + 3 ^ 40 * 6922121 * 2
def baseEnd_6922121 : Nat := 3554375221581216903453251

theorem tailTrace_6922121 : CollatzResearch.WordTrace tailWord_6922121 prefixEnd_6922121 3554375221581216903453251 := by
  unfold tailWord_6922121
  simp only [CollatzResearch.WordTrace]
  refine ⟨252470494155345295991830217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168313662770230197327886811 252470494155345295991830217)
  ·
    refine ⟨189352870616508971993872663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252470494155345295991830217 189352870616508971993872663)
    ·
      refine ⟨284029305924763457990808995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189352870616508971993872663 284029305924763457990808995)
      ·
        refine ⟨426043958887145186986213493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284029305924763457990808995 426043958887145186986213493)
        ·
          refine ⟨39941621145669861279957515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 426043958887145186986213493 39941621145669861279957515)
          ·
            refine ⟨59912431718504791919936273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39941621145669861279957515 59912431718504791919936273)
            ·
              refine ⟨44934323788878593939952205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59912431718504791919936273 44934323788878593939952205)
              ·
                refine ⟨16850371420829472727482077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44934323788878593939952205 16850371420829472727482077)
                ·
                  refine ⟨6318889282811052272805779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16850371420829472727482077 6318889282811052272805779)
                  ·
                    refine ⟨9478333924216578409208669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6318889282811052272805779 9478333924216578409208669)
                    ·
                      refine ⟨3554375221581216903453251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9478333924216578409208669 3554375221581216903453251)
                      ·
                        rfl

theorem cell23_6922121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 3, 3, 1, 3].length) (baseStart_6922121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6922121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6922121 prefixEnd_6922121 := by exact prefixLift 6922121
  have htrace : WordTrace (prefixWord ++ tailWord_6922121) baseStart_6922121 baseEnd_6922121 := by
    simpa [prefixWord, tailWord_6922121, baseEnd_6922121] using wordTrace_append hprefix tailTrace_6922121
  have hstable : (prefixWord ++ tailWord_6922121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6922121).length < 2 ^ (prefixWord ++ tailWord_6922121).sum := by decide
  have hdescent : baseEnd_6922121 < baseStart_6922121 := by decide
  rcases family_descends (prefixWord ++ tailWord_6922121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6922138 : List Nat := [3, 1, 1, 4, 2, 2, 1, 2, 3, 1, 3]
def baseStart_6922138 : Nat := 118140960795 + 6922138 * 2 ^ 59
def prefixEnd_6922138 : Nat := 4983230072969 + 3 ^ 40 * 6922138 * 2
def baseEnd_6922138 : Nat := 3554383950752343336940673

theorem tailTrace_6922138 : CollatzResearch.WordTrace tailWord_6922138 prefixEnd_6922138 3554383950752343336940673 := by
  unfold tailWord_6922138
  simp only [CollatzResearch.WordTrace]
  refine ⟨63117778549070926973799767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168314076130855805263466045 63117778549070926973799767)
  ·
    refine ⟨94676667823606390460699651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63117778549070926973799767 94676667823606390460699651)
    ·
      refine ⟨142015001735409585691049477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94676667823606390460699651 142015001735409585691049477)
      ·
        refine ⟨26627812825389297317071777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142015001735409585691049477 26627812825389297317071777)
        ·
          refine ⟨19970859619041972987803833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26627812825389297317071777 19970859619041972987803833)
          ·
            refine ⟨14978144714281479740852875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19970859619041972987803833 14978144714281479740852875)
            ·
              refine ⟨22467217071422219611279313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14978144714281479740852875 22467217071422219611279313)
              ·
                refine ⟨16850412803566664708459485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22467217071422219611279313 16850412803566664708459485)
                ·
                  refine ⟨6318904801337499265672307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16850412803566664708459485 6318904801337499265672307)
                  ·
                    refine ⟨9478357202006248898508461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6318904801337499265672307 9478357202006248898508461)
                    ·
                      refine ⟨3554383950752343336940673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9478357202006248898508461 3554383950752343336940673)
                      ·
                        rfl

theorem cell23_6922138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_6922138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6922138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6922138 prefixEnd_6922138 := by exact prefixLift 6922138
  have htrace : WordTrace (prefixWord ++ tailWord_6922138) baseStart_6922138 baseEnd_6922138 := by
    simpa [prefixWord, tailWord_6922138, baseEnd_6922138] using wordTrace_append hprefix tailTrace_6922138
  have hstable : (prefixWord ++ tailWord_6922138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6922138).length < 2 ^ (prefixWord ++ tailWord_6922138).sum := by decide
  have hdescent : baseEnd_6922138 < baseStart_6922138 := by decide
  rcases family_descends (prefixWord ++ tailWord_6922138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6922142 : List Nat := [4, 3, 1, 3, 1, 2, 1, 1, 2, 2, 3]
def baseStart_6922142 : Nat := 118140960795 + 6922142 * 2 ^ 59
def prefixEnd_6922142 : Nat := 4983230072969 + 3 ^ 40 * 6922142 * 2
def baseEnd_6922142 : Nat := 3554386004674961321290655

theorem tailTrace_6922142 : CollatzResearch.WordTrace tailWord_6922142 prefixEnd_6922142 3554386004674961321290655 := by
  unfold tailWord_6922142
  simp only [CollatzResearch.WordTrace]
  refine ⟨31558907511033652072293085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168314173392179477718896453 31558907511033652072293085)
  ·
    refine ⟨11834590316637619527109907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31558907511033652072293085 11834590316637619527109907)
    ·
      refine ⟨17751885474956429290664861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11834590316637619527109907 17751885474956429290664861)
      ·
        refine ⟨6656957053108660983999323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17751885474956429290664861 6656957053108660983999323)
        ·
          refine ⟨9985435579662991475998985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6656957053108660983999323 9985435579662991475998985)
          ·
            refine ⟨7489076684747243606999239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9985435579662991475998985 7489076684747243606999239)
            ·
              refine ⟨11233615027120865410498859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7489076684747243606999239 11233615027120865410498859)
              ·
                refine ⟨16850422540681298115748289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11233615027120865410498859 16850422540681298115748289)
                ·
                  refine ⟨12637816905510973586811217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16850422540681298115748289 12637816905510973586811217)
                  ·
                    refine ⟨9478362679133230190108413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12637816905510973586811217 9478362679133230190108413)
                    ·
                      refine ⟨3554386004674961321290655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9478362679133230190108413 3554386004674961321290655)
                      ·
                        rfl

theorem cell23_6922142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_6922142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6922142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6922142 prefixEnd_6922142 := by exact prefixLift 6922142
  have htrace : WordTrace (prefixWord ++ tailWord_6922142) baseStart_6922142 baseEnd_6922142 := by
    simpa [prefixWord, tailWord_6922142, baseEnd_6922142] using wordTrace_append hprefix tailTrace_6922142
  have hstable : (prefixWord ++ tailWord_6922142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6922142).length < 2 ^ (prefixWord ++ tailWord_6922142).sum := by decide
  have hdescent : baseEnd_6922142 < baseStart_6922142 := by decide
  rcases family_descends (prefixWord ++ tailWord_6922142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6922148 : List Nat := [2, 3, 1, 2, 1, 3, 3, 1, 2, 3, 2]
def baseStart_6922148 : Nat := 118140960795 + 6922148 * 2 ^ 59
def prefixEnd_6922148 : Nat := 4983230072969 + 3 ^ 40 * 6922148 * 2
def baseEnd_6922148 : Nat := 3554389085558888297815627

theorem tailTrace_6922148 : CollatzResearch.WordTrace tailWord_6922148 prefixEnd_6922148 3554389085558888297815627 := by
  unfold tailWord_6922148
  simp only [CollatzResearch.WordTrace]
  refine ⟨126235739463123739801531549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168314319284164986402042065 126235739463123739801531549)
  ·
    refine ⟨47338402298671402425574331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126235739463123739801531549 47338402298671402425574331)
    ·
      refine ⟨71007603448007103638361497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47338402298671402425574331 71007603448007103638361497)
      ·
        refine ⟨53255702586005327728771123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71007603448007103638361497 53255702586005327728771123)
        ·
          refine ⟨79883553879007991593156685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53255702586005327728771123 79883553879007991593156685)
          ·
            refine ⟨29956332704627996847433757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79883553879007991593156685 29956332704627996847433757)
            ·
              refine ⟨11233624764235498817787659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29956332704627996847433757 11233624764235498817787659)
              ·
                refine ⟨16850437146353248226681489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11233624764235498817787659 16850437146353248226681489)
                ·
                  refine ⟨12637827859764936170011117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16850437146353248226681489 12637827859764936170011117)
                  ·
                    refine ⟨4739185447411851063754169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12637827859764936170011117 4739185447411851063754169)
                    ·
                      refine ⟨3554389085558888297815627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4739185447411851063754169 3554389085558888297815627)
                      ·
                        rfl

theorem cell23_6922148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 1, 2, 3, 2].length) (baseStart_6922148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6922148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6922148 prefixEnd_6922148 := by exact prefixLift 6922148
  have htrace : WordTrace (prefixWord ++ tailWord_6922148) baseStart_6922148 baseEnd_6922148 := by
    simpa [prefixWord, tailWord_6922148, baseEnd_6922148] using wordTrace_append hprefix tailTrace_6922148
  have hstable : (prefixWord ++ tailWord_6922148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6922148).length < 2 ^ (prefixWord ++ tailWord_6922148).sum := by decide
  have hdescent : baseEnd_6922148 < baseStart_6922148 := by decide
  rcases family_descends (prefixWord ++ tailWord_6922148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6922245 : List Nat := [1, 3, 1, 1, 2, 4, 4, 1, 2, 1, 3]
def baseStart_6922245 : Nat := 118140960795 + 6922245 * 2 ^ 59
def prefixEnd_6922245 : Nat := 4983230072969 + 3 ^ 40 * 6922245 * 2
def baseEnd_6922245 : Nat := 3554438893182374418302681

theorem tailTrace_6922245 : CollatzResearch.WordTrace tailWord_6922245 prefixEnd_6922245 3554438893182374418302681 := by
  unfold tailWord_6922245
  simp only [CollatzResearch.WordTrace]
  refine ⟨252475016806896065169344189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168316677871264043446229459 252475016806896065169344189)
  ·
    refine ⟨94678131302586024438504071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252475016806896065169344189 94678131302586024438504071)
    ·
      refine ⟨142017196953879036657756107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94678131302586024438504071 142017196953879036657756107)
      ·
        refine ⟨213025795430818554986634161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142017196953879036657756107 213025795430818554986634161)
        ·
          refine ⟨159769346573113916239975621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213025795430818554986634161 159769346573113916239975621)
          ·
            refine ⟨29956752482458859294995429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 159769346573113916239975621 29956752482458859294995429)
            ·
              refine ⟨5616891090461036117811643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29956752482458859294995429 5616891090461036117811643)
              ·
                refine ⟨8425336635691554176717465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5616891090461036117811643 8425336635691554176717465)
                ·
                  refine ⟨6319002476768665632538099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8425336635691554176717465 6319002476768665632538099)
                  ·
                    refine ⟨9478503715152998448807149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6319002476768665632538099 9478503715152998448807149)
                    ·
                      refine ⟨3554438893182374418302681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9478503715152998448807149 3554438893182374418302681)
                      ·
                        rfl

theorem cell23_6922245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 4, 1, 2, 1, 3].length) (baseStart_6922245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6922245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6922245 prefixEnd_6922245 := by exact prefixLift 6922245
  have htrace : WordTrace (prefixWord ++ tailWord_6922245) baseStart_6922245 baseEnd_6922245 := by
    simpa [prefixWord, tailWord_6922245, baseEnd_6922245] using wordTrace_append hprefix tailTrace_6922245
  have hstable : (prefixWord ++ tailWord_6922245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6922245).length < 2 ^ (prefixWord ++ tailWord_6922245).sum := by decide
  have hdescent : baseEnd_6922245 < baseStart_6922245 := by decide
  rcases family_descends (prefixWord ++ tailWord_6922245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6922246 : List Nat := [6, 2, 1, 2, 1, 2, 1, 2, 1, 1, 4]
def baseStart_6922246 : Nat := 118140960795 + 6922246 * 2 ^ 59
def prefixEnd_6922246 : Nat := 4983230072969 + 3 ^ 40 * 6922246 * 2
def baseEnd_6922246 : Nat := 3554439406663028914390177

theorem tailTrace_6922246 : CollatzResearch.WordTrace tailWord_6922246 prefixEnd_6922246 3554439406663028914390177 := by
  unfold tailWord_6922246
  simp only [CollatzResearch.WordTrace]
  refine ⟨7889845414996638823129081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 168316702186594961560087061 7889845414996638823129081)
  ·
    refine ⟨5917384061247479117346811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7889845414996638823129081 5917384061247479117346811)
    ·
      refine ⟨8876076091871218676020217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5917384061247479117346811 8876076091871218676020217)
      ·
        refine ⟨6657057068903414007015163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8876076091871218676020217 6657057068903414007015163)
        ·
          refine ⟨9985585603355121010522745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6657057068903414007015163 9985585603355121010522745)
          ·
            refine ⟨7489189202516340757892059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9985585603355121010522745 7489189202516340757892059)
            ·
              refine ⟨11233783803774511136838089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7489189202516340757892059 11233783803774511136838089)
              ·
                refine ⟨8425337852830883352628567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11233783803774511136838089 8425337852830883352628567)
                ·
                  refine ⟨12638006779246325028942851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8425337852830883352628567 12638006779246325028942851)
                  ·
                    refine ⟨18957010168869487543414277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12638006779246325028942851 18957010168869487543414277)
                    ·
                      refine ⟨3554439406663028914390177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18957010168869487543414277 3554439406663028914390177)
                      ·
                        rfl

theorem cell23_6922246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_6922246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6922246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6922246 prefixEnd_6922246 := by exact prefixLift 6922246
  have htrace : WordTrace (prefixWord ++ tailWord_6922246) baseStart_6922246 baseEnd_6922246 := by
    simpa [prefixWord, tailWord_6922246, baseEnd_6922246] using wordTrace_append hprefix tailTrace_6922246
  have hstable : (prefixWord ++ tailWord_6922246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6922246).length < 2 ^ (prefixWord ++ tailWord_6922246).sum := by decide
  have hdescent : baseEnd_6922246 < baseStart_6922246 := by decide
  rcases family_descends (prefixWord ++ tailWord_6922246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6922268 : List Nat := [2, 2, 3, 1, 3, 1, 1, 1, 3, 4, 2]
def baseStart_6922268 : Nat := 118140960795 + 6922268 * 2 ^ 59
def prefixEnd_6922268 : Nat := 4983230072969 + 3 ^ 40 * 6922268 * 2
def baseEnd_6922268 : Nat := 3554450703237427828315075

theorem tailTrace_6922268 : CollatzResearch.WordTrace tailWord_6922268 prefixEnd_6922268 3554450703237427828315075 := by
  unfold tailWord_6922268
  simp only [CollatzResearch.WordTrace]
  refine ⟨126237927842906370048715729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168317237123875160064954305 126237927842906370048715729)
  ·
    refine ⟨94678445882179777536536797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126237927842906370048715729 94678445882179777536536797)
    ·
      refine ⟨35504417205817416576201299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94678445882179777536536797 35504417205817416576201299)
      ·
        refine ⟨53256625808726124864301949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35504417205817416576201299 53256625808726124864301949)
        ·
          refine ⟨19971234678272296824113231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53256625808726124864301949 19971234678272296824113231)
          ·
            refine ⟨29956852017408445236169847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19971234678272296824113231 29956852017408445236169847)
            ·
              refine ⟨44935278026112667854254771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29956852017408445236169847 44935278026112667854254771)
              ·
                refine ⟨67402917039169001781382157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44935278026112667854254771 67402917039169001781382157)
                ·
                  refine ⟨25276093889688375668018309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67402917039169001781382157 25276093889688375668018309)
                  ·
                    refine ⟨4739267604316570437753433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25276093889688375668018309 4739267604316570437753433)
                    ·
                      refine ⟨3554450703237427828315075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4739267604316570437753433 3554450703237427828315075)
                      ·
                        rfl

theorem cell23_6922268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 3, 4, 2].length) (baseStart_6922268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6922268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6922268 prefixEnd_6922268 := by exact prefixLift 6922268
  have htrace : WordTrace (prefixWord ++ tailWord_6922268) baseStart_6922268 baseEnd_6922268 := by
    simpa [prefixWord, tailWord_6922268, baseEnd_6922268] using wordTrace_append hprefix tailTrace_6922268
  have hstable : (prefixWord ++ tailWord_6922268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6922268).length < 2 ^ (prefixWord ++ tailWord_6922268).sum := by decide
  have hdescent : baseEnd_6922268 < baseStart_6922268 := by decide
  rcases family_descends (prefixWord ++ tailWord_6922268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6922302 : List Nat := [4, 2, 1, 3, 2, 1, 2, 1, 1, 4, 2]
def baseStart_6922302 : Nat := 118140960795 + 6922302 * 2 ^ 59
def prefixEnd_6922302 : Nat := 4983230072969 + 3 ^ 40 * 6922302 * 2
def baseEnd_6922302 : Nat := 3554468161579680695289919

theorem tailTrace_6922302 : CollatzResearch.WordTrace tailWord_6922302 prefixEnd_6922302 3554468161579680695289919 := by
  unfold tailWord_6922302
  simp only [CollatzResearch.WordTrace]
  refine ⟨31559636970961195488021145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168318063845126375936112773 31559636970961195488021145)
  ·
    refine ⟨23669727728220896616015859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31559636970961195488021145 23669727728220896616015859)
    ·
      refine ⟨35504591592331344924023789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23669727728220896616015859 35504591592331344924023789)
      ·
        refine ⟨13314221847124254346508921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35504591592331344924023789 13314221847124254346508921)
        ·
          refine ⟨9985666385343190759881691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13314221847124254346508921 9985666385343190759881691)
          ·
            refine ⟨14978499578014786139822537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9985666385343190759881691 14978499578014786139822537)
            ·
              refine ⟨11233874683511089604866903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14978499578014786139822537 11233874683511089604866903)
              ·
                refine ⟨16850812025266634407300355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11233874683511089604866903 16850812025266634407300355)
                ·
                  refine ⟨25276218037899951610950533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16850812025266634407300355 25276218037899951610950533)
                  ·
                    refine ⟨4739290882106240927053225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25276218037899951610950533 4739290882106240927053225)
                    ·
                      refine ⟨3554468161579680695289919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4739290882106240927053225 3554468161579680695289919)
                      ·
                        rfl

theorem cell23_6922302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_6922302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6922302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6922302 prefixEnd_6922302 := by exact prefixLift 6922302
  have htrace : WordTrace (prefixWord ++ tailWord_6922302) baseStart_6922302 baseEnd_6922302 := by
    simpa [prefixWord, tailWord_6922302, baseEnd_6922302] using wordTrace_append hprefix tailTrace_6922302
  have hstable : (prefixWord ++ tailWord_6922302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6922302).length < 2 ^ (prefixWord ++ tailWord_6922302).sum := by decide
  have hdescent : baseEnd_6922302 < baseStart_6922302 := by decide
  rcases family_descends (prefixWord ++ tailWord_6922302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6922358 : List Nat := [5, 1, 1, 2, 1, 2, 1, 2, 1, 3, 4]
def baseStart_6922358 : Nat := 118140960795 + 6922358 * 2 ^ 59
def prefixEnd_6922358 : Nat := 4983230072969 + 3 ^ 40 * 6922358 * 2
def baseEnd_6922358 : Nat := 3554496916496332476189661

theorem tailTrace_6922358 : CollatzResearch.WordTrace tailWord_6922358 prefixEnd_6922358 3554496916496332476189661 := by
  unfold tailWord_6922358
  simp only [CollatzResearch.WordTrace]
  refine ⟨15779946140967917841762983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 168319425503657790312138485 15779946140967917841762983)
  ·
    refine ⟨23669919211451876762644475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15779946140967917841762983 23669919211451876762644475)
    ·
      refine ⟨35504878817177815143966713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23669919211451876762644475 35504878817177815143966713)
      ·
        refine ⟨26628659112883361357975035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35504878817177815143966713 26628659112883361357975035)
        ·
          refine ⟨39942988669325042036962553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26628659112883361357975035 39942988669325042036962553)
          ·
            refine ⟨29957241501993781527721915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39942988669325042036962553 29957241501993781527721915)
            ·
              refine ⟨44935862252990672291582873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29957241501993781527721915 44935862252990672291582873)
              ·
                refine ⟨33701896689743004218687155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44935862252990672291582873 33701896689743004218687155)
                ·
                  refine ⟨50552845034614506328030733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33701896689743004218687155 50552845034614506328030733)
                  ·
                    refine ⟨18957316887980439873011525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50552845034614506328030733 18957316887980439873011525)
                    ·
                      refine ⟨3554496916496332476189661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18957316887980439873011525 3554496916496332476189661)
                      ·
                        rfl

theorem cell23_6922358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_6922358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6922358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6922358 prefixEnd_6922358 := by exact prefixLift 6922358
  have htrace : WordTrace (prefixWord ++ tailWord_6922358) baseStart_6922358 baseEnd_6922358 := by
    simpa [prefixWord, tailWord_6922358, baseEnd_6922358] using wordTrace_append hprefix tailTrace_6922358
  have hstable : (prefixWord ++ tailWord_6922358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6922358).length < 2 ^ (prefixWord ++ tailWord_6922358).sum := by decide
  have hdescent : baseEnd_6922358 < baseStart_6922358 := by decide
  rcases family_descends (prefixWord ++ tailWord_6922358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6922378 : List Nat := [3, 1, 2, 3, 1, 2, 2, 1, 1, 4, 3]
def baseStart_6922378 : Nat := 118140960795 + 6922378 * 2 ^ 59
def prefixEnd_6922378 : Nat := 4983230072969 + 3 ^ 40 * 6922378 * 2
def baseEnd_6922378 : Nat := 3554507186109422397939569

theorem tailTrace_6922378 : CollatzResearch.WordTrace tailWord_6922378 prefixEnd_6922378 3554507186109422397939569 := by
  unfold tailWord_6922378
  simp only [CollatzResearch.WordTrace]
  refine ⟨63119966928853557220983947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168319911810276152589290525 63119966928853557220983947)
  ·
    refine ⟨94679950393280335831475921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63119966928853557220983947 94679950393280335831475921)
    ·
      refine ⟨71009962794960251873606941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94679950393280335831475921 71009962794960251873606941)
      ·
        refine ⟨26628736048110094452602603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71009962794960251873606941 26628736048110094452602603)
        ·
          refine ⟨39943104072165141678903905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26628736048110094452602603 39943104072165141678903905)
          ·
            refine ⟨29957328054123856259177929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39943104072165141678903905 29957328054123856259177929)
            ·
              refine ⟨22467996040592892194383447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29957328054123856259177929 22467996040592892194383447)
              ·
                refine ⟨33701994060889338291575171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22467996040592892194383447 33701994060889338291575171)
                ·
                  refine ⟨50552991091334007437362757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33701994060889338291575171 50552991091334007437362757)
                  ·
                    refine ⟨9478685829625126394505517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50552991091334007437362757 9478685829625126394505517)
                    ·
                      refine ⟨3554507186109422397939569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9478685829625126394505517 3554507186109422397939569)
                      ·
                        rfl

theorem cell23_6922378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_6922378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6922378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6922378 prefixEnd_6922378 := by exact prefixLift 6922378
  have htrace : WordTrace (prefixWord ++ tailWord_6922378) baseStart_6922378 baseEnd_6922378 := by
    simpa [prefixWord, tailWord_6922378, baseEnd_6922378] using wordTrace_append hprefix tailTrace_6922378
  have hstable : (prefixWord ++ tailWord_6922378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6922378).length < 2 ^ (prefixWord ++ tailWord_6922378).sum := by decide
  have hdescent : baseEnd_6922378 < baseStart_6922378 := by decide
  rcases family_descends (prefixWord ++ tailWord_6922378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6922402 : List Nat := [3, 3, 1, 3, 1, 3, 1, 1, 3, 4]
def baseStart_6922402 : Nat := 118140960795 + 6922402 * 2 ^ 59
def prefixEnd_6922402 : Nat := 4983230072969 + 3 ^ 40 * 6922402 * 2
def baseEnd_6922402 : Nat := 1184839836548376768013153

theorem tailTrace_6922402 : CollatzResearch.WordTrace tailWord_6922402 prefixEnd_6922402 1184839836548376768013153 := by
  unfold tailWord_6922402
  simp only [CollatzResearch.WordTrace]
  refine ⟨63120185766831820245702365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168320495378218187321872973 63120185766831820245702365)
  ·
    refine ⟨23670069662561932592138387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63120185766831820245702365 23670069662561932592138387)
    ·
      refine ⟨35505104493842898888207581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23670069662561932592138387 35505104493842898888207581)
      ·
        refine ⟨13314414185191087083077843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35505104493842898888207581 13314414185191087083077843)
        ·
          refine ⟨19971621277786630624616765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13314414185191087083077843 19971621277786630624616765)
          ·
            refine ⟨7489357979169986484231287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19971621277786630624616765 7489357979169986484231287)
            ·
              refine ⟨11234036968754979726346931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7489357979169986484231287 11234036968754979726346931)
              ·
                refine ⟨16851055453132469589520397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11234036968754979726346931 16851055453132469589520397)
                ·
                  refine ⟨6319145794924676096070149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16851055453132469589520397 6319145794924676096070149)
                  ·
                    refine ⟨1184839836548376768013153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6319145794924676096070149 1184839836548376768013153)
                    ·
                      rfl

theorem cell23_6922402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 1, 3, 4].length) (baseStart_6922402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6922402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6922402 prefixEnd_6922402 := by exact prefixLift 6922402
  have htrace : WordTrace (prefixWord ++ tailWord_6922402) baseStart_6922402 baseEnd_6922402 := by
    simpa [prefixWord, tailWord_6922402, baseEnd_6922402] using wordTrace_append hprefix tailTrace_6922402
  have hstable : (prefixWord ++ tailWord_6922402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6922402).length < 2 ^ (prefixWord ++ tailWord_6922402).sum := by decide
  have hdescent : baseEnd_6922402 < baseStart_6922402 := by decide
  rcases family_descends (prefixWord ++ tailWord_6922402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6922442 : List Nat := [3, 1, 2, 1, 3, 1, 2, 5, 1, 1, 3]
def baseStart_6922442 : Nat := 118140960795 + 6922442 * 2 ^ 59
def prefixEnd_6922442 : Nat := 4983230072969 + 3 ^ 40 * 6922442 * 2
def baseEnd_6922442 : Nat := 3554540048871310147539275

theorem tailTrace_6922442 : CollatzResearch.WordTrace tailWord_6922442 prefixEnd_6922442 3554540048871310147539275 := by
  unfold tailWord_6922442
  simp only [CollatzResearch.WordTrace]
  refine ⟨63120550496795591953566395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168321467991454911876177053 63120550496795591953566395)
  ·
    refine ⟨94680825745193387930349593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63120550496795591953566395 94680825745193387930349593)
    ·
      refine ⟨71010619308895040947762195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94680825745193387930349593 71010619308895040947762195)
      ·
        refine ⟨106515928963342561421643293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71010619308895040947762195 106515928963342561421643293)
        ·
          refine ⟨39943473361253460533116235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106515928963342561421643293 39943473361253460533116235)
          ·
            refine ⟨59915210041880190799674353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39943473361253460533116235 59915210041880190799674353)
            ·
              refine ⟨44936407531410143099755765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59915210041880190799674353 44936407531410143099755765)
              ·
                refine ⟨4212788206069700915602103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44936407531410143099755765 4212788206069700915602103)
                ·
                  refine ⟨6319182309104551373403155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4212788206069700915602103 6319182309104551373403155)
                  ·
                    refine ⟨9478773463656827060104733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6319182309104551373403155 9478773463656827060104733)
                    ·
                      refine ⟨3554540048871310147539275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9478773463656827060104733 3554540048871310147539275)
                      ·
                        rfl

theorem cell23_6922442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 5, 1, 1, 3].length) (baseStart_6922442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6922442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6922442 prefixEnd_6922442 := by exact prefixLift 6922442
  have htrace : WordTrace (prefixWord ++ tailWord_6922442) baseStart_6922442 baseEnd_6922442 := by
    simpa [prefixWord, tailWord_6922442, baseEnd_6922442] using wordTrace_append hprefix tailTrace_6922442
  have hstable : (prefixWord ++ tailWord_6922442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6922442).length < 2 ^ (prefixWord ++ tailWord_6922442).sum := by decide
  have hdescent : baseEnd_6922442 < baseStart_6922442 := by decide
  rcases family_descends (prefixWord ++ tailWord_6922442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6922458 : List Nat := [3, 1, 1, 2, 2, 1, 2, 3, 4, 4]
def baseStart_6922458 : Nat := 118140960795 + 6922458 * 2 ^ 59
def prefixEnd_6922458 : Nat := 4983230072969 + 3 ^ 40 * 6922458 * 2
def baseEnd_6922458 : Nat := 1184849421520594028313067

theorem tailTrace_6922458 : CollatzResearch.WordTrace tailWord_6922458 prefixEnd_6922458 1184849421520594028313067 := by
  unfold tailWord_6922458
  simp only [CollatzResearch.WordTrace]
  refine ⟨63120696388781100636712007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168321857036749601697898685 63120696388781100636712007)
  ·
    refine ⟨94681044583171650955068011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63120696388781100636712007 94681044583171650955068011)
    ·
      refine ⟨142021566874757476432602017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94681044583171650955068011 142021566874757476432602017)
      ·
        refine ⟨106516175156068107324451513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142021566874757476432602017 106516175156068107324451513)
        ·
          refine ⟨79887131367051080493338635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106516175156068107324451513 79887131367051080493338635)
          ·
            refine ⟨119830697050576620740007953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79887131367051080493338635 119830697050576620740007953)
            ·
              refine ⟨89873022787932465555005965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119830697050576620740007953 89873022787932465555005965)
              ·
                refine ⟨33702383545474674583127237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89873022787932465555005965 33702383545474674583127237)
                ·
                  refine ⟨6319196914776501484336357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33702383545474674583127237 6319196914776501484336357)
                  ·
                    refine ⟨1184849421520594028313067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6319196914776501484336357 1184849421520594028313067)
                    ·
                      rfl

theorem cell23_6922458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 4, 4].length) (baseStart_6922458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6922458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6922458 prefixEnd_6922458 := by exact prefixLift 6922458
  have htrace : WordTrace (prefixWord ++ tailWord_6922458) baseStart_6922458 baseEnd_6922458 := by
    simpa [prefixWord, tailWord_6922458, baseEnd_6922458] using wordTrace_append hprefix tailTrace_6922458
  have hstable : (prefixWord ++ tailWord_6922458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6922458).length < 2 ^ (prefixWord ++ tailWord_6922458).sum := by decide
  have hdescent : baseEnd_6922458 < baseStart_6922458 := by decide
  rcases family_descends (prefixWord ++ tailWord_6922458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6922482 : List Nat := [3, 2, 1, 3, 2, 1, 1, 1, 5, 2, 2]
def baseStart_6922482 : Nat := 118140960795 + 6922482 * 2 ^ 59
def prefixEnd_6922482 : Nat := 4983230072969 + 3 ^ 40 * 6922482 * 2
def baseEnd_6922482 : Nat := 3554560588097489991039091

theorem tailTrace_6922482 : CollatzResearch.WordTrace tailWord_6922482 prefixEnd_6922482 3554560588097489991039091 := by
  unfold tailWord_6922482
  simp only [CollatzResearch.WordTrace]
  refine ⟨63120915226759363661430425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168322440604691636430481133 63120915226759363661430425)
  ·
    refine ⟨47340686420069522746072819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63120915226759363661430425 47340686420069522746072819)
    ·
      refine ⟨71011029630104284119109229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47340686420069522746072819 71011029630104284119109229)
      ·
        refine ⟨26629136111289106544665961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71011029630104284119109229 26629136111289106544665961)
        ·
          refine ⟨19971852083466829908499471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26629136111289106544665961 19971852083466829908499471)
          ·
            refine ⟨29957778125200244862749207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19971852083466829908499471 29957778125200244862749207)
            ·
              refine ⟨44936667187800367294123811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29957778125200244862749207 44936667187800367294123811)
              ·
                refine ⟨67405000781700550941185717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44936667187800367294123811 67405000781700550941185717)
                ·
                  refine ⟨6319218823284426650736161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67405000781700550941185717 6319218823284426650736161)
                  ·
                    refine ⟨4739414117463319988052121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6319218823284426650736161 4739414117463319988052121)
                    ·
                      refine ⟨3554560588097489991039091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4739414117463319988052121 3554560588097489991039091)
                      ·
                        rfl

theorem cell23_6922482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 5, 2, 2].length) (baseStart_6922482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6922482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6922482 prefixEnd_6922482 := by exact prefixLift 6922482
  have htrace : WordTrace (prefixWord ++ tailWord_6922482) baseStart_6922482 baseEnd_6922482 := by
    simpa [prefixWord, tailWord_6922482, baseEnd_6922482] using wordTrace_append hprefix tailTrace_6922482
  have hstable : (prefixWord ++ tailWord_6922482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6922482).length < 2 ^ (prefixWord ++ tailWord_6922482).sum := by decide
  have hdescent : baseEnd_6922482 < baseStart_6922482 := by decide
  rcases family_descends (prefixWord ++ tailWord_6922482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6922499 : List Nat := [1, 1, 1, 3, 2, 3, 4, 3, 1, 2, 2]
def baseStart_6922499 : Nat := 118140960795 + 6922499 * 2 ^ 59
def prefixEnd_6922499 : Nat := 4983230072969 + 3 ^ 40 * 6922499 * 2
def baseEnd_6922499 : Nat := 3554569317268616424526513

theorem tailTrace_6922499 : CollatzResearch.WordTrace tailWord_6922499 prefixEnd_6922499 3554569317268616424526513 := by
  unfold tailWord_6922499
  simp only [CollatzResearch.WordTrace]
  refine ⟨252484280947975866549090551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168322853965317244366060367 252484280947975866549090551)
  ·
    refine ⟨378726421421963799823635827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252484280947975866549090551 378726421421963799823635827)
    ·
      refine ⟨568089632132945699735453741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378726421421963799823635827 568089632132945699735453741)
      ·
        refine ⟨213033612049854637400795153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 568089632132945699735453741 213033612049854637400795153)
        ·
          refine ⟨159775209037390978050596365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213033612049854637400795153 159775209037390978050596365)
          ·
            refine ⟨59915703389021616768973637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159775209037390978050596365 59915703389021616768973637)
            ·
              refine ⟨11234194385441553144182557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59915703389021616768973637 11234194385441553144182557)
              ·
                refine ⟨4212822894540582429068459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11234194385441553144182557 4212822894540582429068459)
                ·
                  refine ⟨6319234341810873643602689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4212822894540582429068459 6319234341810873643602689)
                  ·
                    refine ⟨4739425756358155232702017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6319234341810873643602689 4739425756358155232702017)
                    ·
                      refine ⟨3554569317268616424526513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4739425756358155232702017 3554569317268616424526513)
                      ·
                        rfl

theorem cell23_6922499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 3, 1, 2, 2].length) (baseStart_6922499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6922499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6922499 prefixEnd_6922499 := by exact prefixLift 6922499
  have htrace : WordTrace (prefixWord ++ tailWord_6922499) baseStart_6922499 baseEnd_6922499 := by
    simpa [prefixWord, tailWord_6922499, baseEnd_6922499] using wordTrace_append hprefix tailTrace_6922499
  have hstable : (prefixWord ++ tailWord_6922499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6922499).length < 2 ^ (prefixWord ++ tailWord_6922499).sum := by decide
  have hdescent : baseEnd_6922499 < baseStart_6922499 := by decide
  rcases family_descends (prefixWord ++ tailWord_6922499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6922501 : List Nat := [1, 3, 1, 1, 2, 1, 2, 2, 1, 9]
def baseStart_6922501 : Nat := 118140960795 + 6922501 * 2 ^ 59
def prefixEnd_6922501 : Nat := 4983230072969 + 3 ^ 40 * 6922501 * 2
def baseEnd_6922501 : Nat := 1184856781409975138900501

theorem tailTrace_6922501 : CollatzResearch.WordTrace tailWord_6922501 prefixEnd_6922501 1184856781409975138900501 := by
  unfold tailWord_6922501
  simp only [CollatzResearch.WordTrace]
  refine ⟨252484353893968620890663357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168322902595979080593775571 252484353893968620890663357)
  ·
    refine ⟨94681632710238232833998759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252484353893968620890663357 94681632710238232833998759)
    ·
      refine ⟨142022449065357349250998139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94681632710238232833998759 142022449065357349250998139)
      ·
        refine ⟨213033673598036023876497209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142022449065357349250998139 213033673598036023876497209)
        ·
          refine ⟨159775255198527017907372907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213033673598036023876497209 159775255198527017907372907)
          ·
            refine ⟨239662882797790526861059361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159775255198527017907372907 239662882797790526861059361)
            ·
              refine ⟨179747162098342895145794521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 239662882797790526861059361 179747162098342895145794521)
              ·
                refine ⟨134810371573757171359345891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179747162098342895145794521 134810371573757171359345891)
                ·
                  refine ⟨202215557360635757039018837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134810371573757171359345891 202215557360635757039018837)
                  ·
                    refine ⟨1184856781409975138900501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 202215557360635757039018837 1184856781409975138900501)
                    ·
                      rfl

theorem cell23_6922501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 9].length) (baseStart_6922501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6922501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6922501 prefixEnd_6922501 := by exact prefixLift 6922501
  have htrace : WordTrace (prefixWord ++ tailWord_6922501) baseStart_6922501 baseEnd_6922501 := by
    simpa [prefixWord, tailWord_6922501, baseEnd_6922501] using wordTrace_append hprefix tailTrace_6922501
  have hstable : (prefixWord ++ tailWord_6922501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6922501).length < 2 ^ (prefixWord ++ tailWord_6922501).sum := by decide
  have hdescent : baseEnd_6922501 < baseStart_6922501 := by decide
  rcases family_descends (prefixWord ++ tailWord_6922501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6922526 : List Nat := [4, 3, 2, 1, 1, 2, 3, 1, 2, 4]
def baseStart_6922526 : Nat := 118140960795 + 6922526 * 2 ^ 59
def prefixEnd_6922526 : Nat := 4983230072969 + 3 ^ 40 * 6922526 * 2
def baseEnd_6922526 : Nat := 1184861060415429272962963

theorem tailTrace_6922526 : CollatzResearch.WordTrace tailWord_6922526 prefixEnd_6922526 1184861060415429272962963 := by
  unfold tailWord_6922526
  simp only [CollatzResearch.WordTrace]
  refine ⟨31560658214859756270040429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168323510479252033440215621 31560658214859756270040429)
  ·
    refine ⟨11835246830572408601265161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31560658214859756270040429 11835246830572408601265161)
    ·
      refine ⟨8876435122929306450948871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11835246830572408601265161 8876435122929306450948871)
      ·
        refine ⟨13314652684393959676423307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8876435122929306450948871 13314652684393959676423307)
        ·
          refine ⟨19971979026590939514634961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13314652684393959676423307 19971979026590939514634961)
          ·
            refine ⟨14978984269943204635976221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19971979026590939514634961 14978984269943204635976221)
            ·
              refine ⟨5617119101228701738491083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14978984269943204635976221 5617119101228701738491083)
              ·
                refine ⟨8425678651843052607736625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5617119101228701738491083 8425678651843052607736625)
                ·
                  refine ⟨6319258988882289455802469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8425678651843052607736625 6319258988882289455802469)
                  ·
                    refine ⟨1184861060415429272962963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6319258988882289455802469 1184861060415429272962963)
                    ·
                      rfl

theorem cell23_6922526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_6922526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6922526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6922526 prefixEnd_6922526 := by exact prefixLift 6922526
  have htrace : WordTrace (prefixWord ++ tailWord_6922526) baseStart_6922526 baseEnd_6922526 := by
    simpa [prefixWord, tailWord_6922526, baseEnd_6922526] using wordTrace_append hprefix tailTrace_6922526
  have hstable : (prefixWord ++ tailWord_6922526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6922526).length < 2 ^ (prefixWord ++ tailWord_6922526).sum := by decide
  have hdescent : baseEnd_6922526 < baseStart_6922526 := by decide
  rcases family_descends (prefixWord ++ tailWord_6922526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6922532 : List Nat := [2, 3, 1, 3, 1, 4, 1, 1, 1, 3, 3]
def baseStart_6922532 : Nat := 118140960795 + 6922532 * 2 ^ 59
def prefixEnd_6922532 : Nat := 4983230072969 + 3 ^ 40 * 6922532 * 2
def baseEnd_6922532 : Nat := 3554586262130214795413861

theorem tailTrace_6922532 : CollatzResearch.WordTrace tailWord_6922532 prefixEnd_6922532 3554586262130214795413861 := by
  unfold tailWord_6922532
  simp only [CollatzResearch.WordTrace]
  refine ⟨126242742278428156592520925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168323656371237542123361233 126242742278428156592520925)
  ·
    refine ⟨47341028354410558722195347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126242742278428156592520925 47341028354410558722195347)
    ·
      refine ⟨71011542531615838083293021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47341028354410558722195347 71011542531615838083293021)
      ·
        refine ⟨26629328449355939281234883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71011542531615838083293021 26629328449355939281234883)
        ·
          refine ⟨39943992674033908921852325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26629328449355939281234883 39943992674033908921852325)
          ·
            refine ⟨7489498626381357922847311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39943992674033908921852325 7489498626381357922847311)
            ·
              refine ⟨11234247939572036884270967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7489498626381357922847311 11234247939572036884270967)
              ·
                refine ⟨16851371909358055326406451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11234247939572036884270967 16851371909358055326406451)
                ·
                  refine ⟨25277057864037082989609677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16851371909358055326406451 25277057864037082989609677)
                  ·
                    refine ⟨9478896699013906121103629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25277057864037082989609677 9478896699013906121103629)
                    ·
                      refine ⟨3554586262130214795413861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9478896699013906121103629 3554586262130214795413861)
                      ·
                        rfl

theorem cell23_6922532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_6922532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6922532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6922532 prefixEnd_6922532 := by exact prefixLift 6922532
  have htrace : WordTrace (prefixWord ++ tailWord_6922532) baseStart_6922532 baseEnd_6922532 := by
    simpa [prefixWord, tailWord_6922532, baseEnd_6922532] using wordTrace_append hprefix tailTrace_6922532
  have hstable : (prefixWord ++ tailWord_6922532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6922532).length < 2 ^ (prefixWord ++ tailWord_6922532).sum := by decide
  have hdescent : baseEnd_6922532 < baseStart_6922532 := by decide
  rcases family_descends (prefixWord ++ tailWord_6922532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6922568 : List Nat := [2, 1, 3, 1, 1, 2, 2, 1, 4, 2, 4]
def baseStart_6922568 : Nat := 118140960795 + 6922568 * 2 ^ 59
def prefixEnd_6922568 : Nat := 4983230072969 + 3 ^ 40 * 6922568 * 2
def baseEnd_6922568 : Nat := 3554604747433776654563695

theorem tailTrace_6922568 : CollatzResearch.WordTrace tailWord_6922568 prefixEnd_6922568 3554604747433776654563695 := by
  unfold tailWord_6922568
  simp only [CollatzResearch.WordTrace]
  refine ⟨126243398792362945666676179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168324531723150594222234905 126243398792362945666676179)
  ·
    refine ⟨189365098188544418500014269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126243398792362945666676179 189365098188544418500014269)
    ·
      refine ⟨71011911820704156937505351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189365098188544418500014269 71011911820704156937505351)
      ·
        refine ⟨106517867731056235406258027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71011911820704156937505351 106517867731056235406258027)
        ·
          refine ⟨159776801596584353109387041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106517867731056235406258027 159776801596584353109387041)
          ·
            refine ⟨119832601197438264832040281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159776801596584353109387041 119832601197438264832040281)
            ·
              refine ⟨89874450898078698624030211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119832601197438264832040281 89874450898078698624030211)
              ·
                refine ⟨134811676347118047936045317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89874450898078698624030211 134811676347118047936045317)
                ·
                  refine ⟨25277189315084633988008497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 134811676347118047936045317 25277189315084633988008497)
                  ·
                    refine ⟨18957891986313475491006373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25277189315084633988008497 18957891986313475491006373)
                    ·
                      refine ⟨3554604747433776654563695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18957891986313475491006373 3554604747433776654563695)
                      ·
                        rfl

theorem cell23_6922568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 4, 2, 4].length) (baseStart_6922568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6922568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6922568 prefixEnd_6922568 := by exact prefixLift 6922568
  have htrace : WordTrace (prefixWord ++ tailWord_6922568) baseStart_6922568 baseEnd_6922568 := by
    simpa [prefixWord, tailWord_6922568, baseEnd_6922568] using wordTrace_append hprefix tailTrace_6922568
  have hstable : (prefixWord ++ tailWord_6922568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6922568).length < 2 ^ (prefixWord ++ tailWord_6922568).sum := by decide
  have hdescent : baseEnd_6922568 < baseStart_6922568 := by decide
  rcases family_descends (prefixWord ++ tailWord_6922568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6922572 : List Nat := [2, 2, 1, 3, 2, 1, 1, 3, 4, 2, 2]
def baseStart_6922572 : Nat := 118140960795 + 6922572 * 2 ^ 59
def prefixEnd_6922572 : Nat := 4983230072969 + 3 ^ 40 * 6922572 * 2
def baseEnd_6922572 : Nat := 3554606801356394638913677

theorem tailTrace_6922572 : CollatzResearch.WordTrace tailWord_6922572 prefixEnd_6922572 3554606801356394638913677 := by
  unfold tailWord_6922572
  simp only [CollatzResearch.WordTrace]
  refine ⟨126243471738355700008248985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168324628984474266677665313 126243471738355700008248985)
  ·
    refine ⟨94682603803766775006186739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126243471738355700008248985 94682603803766775006186739)
    ·
      refine ⟨142023905705650162509280109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94682603803766775006186739 142023905705650162509280109)
      ·
        refine ⟨53258964639618810940980041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142023905705650162509280109 53258964639618810940980041)
        ·
          refine ⟨39944223479714108205735031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53258964639618810940980041 39944223479714108205735031)
          ·
            refine ⟨59916335219571162308602547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39944223479714108205735031 59916335219571162308602547)
            ·
              refine ⟨89874502829356743462903821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59916335219571162308602547 89874502829356743462903821)
              ·
                refine ⟨33702938561008778798588933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89874502829356743462903821 33702938561008778798588933)
                ·
                  refine ⟨6319300980189146024735425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33702938561008778798588933 6319300980189146024735425)
                  ·
                    refine ⟨4739475735141859518551569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6319300980189146024735425 4739475735141859518551569)
                    ·
                      refine ⟨3554606801356394638913677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4739475735141859518551569 3554606801356394638913677)
                      ·
                        rfl

theorem cell23_6922572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 4, 2, 2].length) (baseStart_6922572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6922572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6922572 prefixEnd_6922572 := by exact prefixLift 6922572
  have htrace : WordTrace (prefixWord ++ tailWord_6922572) baseStart_6922572 baseEnd_6922572 := by
    simpa [prefixWord, tailWord_6922572, baseEnd_6922572] using wordTrace_append hprefix tailTrace_6922572
  have hstable : (prefixWord ++ tailWord_6922572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6922572).length < 2 ^ (prefixWord ++ tailWord_6922572).sum := by decide
  have hdescent : baseEnd_6922572 < baseStart_6922572 := by decide
  rcases family_descends (prefixWord ++ tailWord_6922572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6922646 : List Nat := [5, 3, 1, 2, 1, 1, 1, 2, 7]
def baseStart_6922646 : Nat := 118140960795 + 6922646 * 2 ^ 59
def prefixEnd_6922646 : Nat := 4983230072969 + 3 ^ 40 * 6922646 * 2
def baseEnd_6922646 : Nat := 394960533213869705487593

theorem tailTrace_6922646 : CollatzResearch.WordTrace tailWord_6922646 prefixEnd_6922646 394960533213869705487593 := by
  unfold tailWord_6922646
  simp only [CollatzResearch.WordTrace]
  refine ⟨15780602654902706915918237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 168326428318962207103127861 15780602654902706915918237)
  ·
    refine ⟨5917725995588515093469339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15780602654902706915918237 5917725995588515093469339)
    ·
      refine ⟨8876588993382772640204009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5917725995588515093469339 8876588993382772640204009)
      ·
        refine ⟨6657441745037079480153007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8876588993382772640204009 6657441745037079480153007)
        ·
          refine ⟨9986162617555619220229511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6657441745037079480153007 9986162617555619220229511)
          ·
            refine ⟨14979243926333428830344267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9986162617555619220229511 14979243926333428830344267)
            ·
              refine ⟨22468865889500143245516401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14979243926333428830344267 22468865889500143245516401)
              ·
                refine ⟨16851649417125107434137301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22468865889500143245516401 16851649417125107434137301)
                ·
                  refine ⟨394960533213869705487593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16851649417125107434137301 394960533213869705487593)
                  ·
                    rfl

theorem cell23_6922646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_6922646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6922646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6922646 prefixEnd_6922646 := by exact prefixLift 6922646
  have htrace : WordTrace (prefixWord ++ tailWord_6922646) baseStart_6922646 baseEnd_6922646 := by
    simpa [prefixWord, tailWord_6922646, baseEnd_6922646] using wordTrace_append hprefix tailTrace_6922646
  have hstable : (prefixWord ++ tailWord_6922646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6922646).length < 2 ^ (prefixWord ++ tailWord_6922646).sum := by decide
  have hdescent : baseEnd_6922646 < baseStart_6922646 := by decide
  rcases family_descends (prefixWord ++ tailWord_6922646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6922668 : List Nat := [2, 2, 1, 1, 1, 1, 3, 4, 8]
def baseStart_6922668 : Nat := 118140960795 + 6922668 * 2 ^ 59
def prefixEnd_6922668 : Nat := 4983230072969 + 3 ^ 40 * 6922668 * 2
def baseEnd_6922668 : Nat := 394961788388802918145915

theorem tailTrace_6922668 : CollatzResearch.WordTrace tailWord_6922668 prefixEnd_6922668 394961788388802918145915 := by
  unfold tailWord_6922668
  simp only [CollatzResearch.WordTrace]
  refine ⟨126245222442181804205996329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168326963256242405607995105 126245222442181804205996329)
  ·
    refine ⟨94683916831636353154497247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126245222442181804205996329 94683916831636353154497247)
    ·
      refine ⟨142025875247454529731745871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94683916831636353154497247 142025875247454529731745871)
      ·
        refine ⟨213038812871181794597618807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142025875247454529731745871 213038812871181794597618807)
        ·
          refine ⟨319558219306772691896428211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213038812871181794597618807 319558219306772691896428211)
          ·
            refine ⟨479337328960159037844642317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319558219306772691896428211 479337328960159037844642317)
            ·
              refine ⟨179751498360059639191740869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 479337328960159037844642317 179751498360059639191740869)
              ·
                refine ⟨33703405942511182348451413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 179751498360059639191740869 33703405942511182348451413)
                ·
                  refine ⟨394961788388802918145915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33703405942511182348451413 394961788388802918145915)
                  ·
                    rfl

theorem cell23_6922668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 8].length) (baseStart_6922668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6922668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6922668 prefixEnd_6922668 := by exact prefixLift 6922668
  have htrace : WordTrace (prefixWord ++ tailWord_6922668) baseStart_6922668 baseEnd_6922668 := by
    simpa [prefixWord, tailWord_6922668, baseEnd_6922668] using wordTrace_append hprefix tailTrace_6922668
  have hstable : (prefixWord ++ tailWord_6922668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6922668).length < 2 ^ (prefixWord ++ tailWord_6922668).sum := by decide
  have hdescent : baseEnd_6922668 < baseStart_6922668 := by decide
  rcases family_descends (prefixWord ++ tailWord_6922668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6922685 : List Nat := [1, 4, 1, 2, 2, 3, 1, 1, 8]
def baseStart_6922685 : Nat := 118140960795 + 6922685 * 2 ^ 59
def prefixEnd_6922685 : Nat := 4983230072969 + 3 ^ 40 * 6922685 * 2
def baseEnd_6922685 : Nat := 394962758296705855200073

theorem tailTrace_6922685 : CollatzResearch.WordTrace tailWord_6922685 prefixEnd_6922685 394962758296705855200073 := by
  unfold tailWord_6922685
  simp only [CollatzResearch.WordTrace]
  refine ⟨252491064925302020315361509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168327376616868013543574339 252491064925302020315361509)
  ·
    refine ⟨47342074673494128809130283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 252491064925302020315361509 47342074673494128809130283)
    ·
      refine ⟨71013112010241193213695425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47342074673494128809130283 71013112010241193213695425)
      ·
        refine ⟨53259834007680894910271569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71013112010241193213695425 53259834007680894910271569)
        ·
          refine ⟨39944875505760671182703677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53259834007680894910271569 39944875505760671182703677)
          ·
            refine ⟨14979328314660251693513879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39944875505760671182703677 14979328314660251693513879)
            ·
              refine ⟨22468992471990377540270819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14979328314660251693513879 22468992471990377540270819)
              ·
                refine ⟨33703488707985566310406229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22468992471990377540270819 33703488707985566310406229)
                ·
                  refine ⟨394962758296705855200073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33703488707985566310406229 394962758296705855200073)
                  ·
                    rfl

theorem cell23_6922685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 8].length) (baseStart_6922685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6922685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6922685 prefixEnd_6922685 := by exact prefixLift 6922685
  have htrace : WordTrace (prefixWord ++ tailWord_6922685) baseStart_6922685 baseEnd_6922685 := by
    simpa [prefixWord, tailWord_6922685, baseEnd_6922685] using wordTrace_append hprefix tailTrace_6922685
  have hstable : (prefixWord ++ tailWord_6922685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6922685).length < 2 ^ (prefixWord ++ tailWord_6922685).sum := by decide
  have hdescent : baseEnd_6922685 < baseStart_6922685 := by decide
  rcases family_descends (prefixWord ++ tailWord_6922685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6922723 : List Nat := [1, 1, 1, 6, 4, 1, 1, 3, 1, 4]
def baseStart_6922723 : Nat := 118140960795 + 6922723 * 2 ^ 59
def prefixEnd_6922723 : Nat := 4983230072969 + 3 ^ 40 * 6922723 * 2
def baseEnd_6922723 : Nat := 1184894778978407849375161

theorem tailTrace_6922723 : CollatzResearch.WordTrace tailWord_6922723 prefixEnd_6922723 1184894778978407849375161 := by
  unfold tailWord_6922723
  simp only [CollatzResearch.WordTrace]
  refine ⟨252492450899164352805244823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168328300599442901870163215 252492450899164352805244823)
  ·
    refine ⟨378738676348746529207867235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252492450899164352805244823 378738676348746529207867235)
    ·
      refine ⟨568108014523119793811800853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378738676348746529207867235 568108014523119793811800853)
      ·
        refine ⟨26630063180771240334928165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 568108014523119793811800853 26630063180771240334928165)
        ·
          refine ⟨4993136846394607562799031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26630063180771240334928165 4993136846394607562799031)
          ·
            refine ⟨7489705269591911344198547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4993136846394607562799031 7489705269591911344198547)
            ·
              refine ⟨11234557904387867016297821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7489705269591911344198547 11234557904387867016297821)
              ·
                refine ⟨4212959214145450131111683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11234557904387867016297821 4212959214145450131111683)
                ·
                  refine ⟨6319438821218175196667525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4212959214145450131111683 6319438821218175196667525)
                  ·
                    refine ⟨1184894778978407849375161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6319438821218175196667525 1184894778978407849375161)
                    ·
                      rfl

theorem cell23_6922723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 3, 1, 4].length) (baseStart_6922723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6922723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6922723 prefixEnd_6922723 := by exact prefixLift 6922723
  have htrace : WordTrace (prefixWord ++ tailWord_6922723) baseStart_6922723 baseEnd_6922723 := by
    simpa [prefixWord, tailWord_6922723, baseEnd_6922723] using wordTrace_append hprefix tailTrace_6922723
  have hstable : (prefixWord ++ tailWord_6922723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6922723).length < 2 ^ (prefixWord ++ tailWord_6922723).sum := by decide
  have hdescent : baseEnd_6922723 < baseStart_6922723 := by decide
  rcases family_descends (prefixWord ++ tailWord_6922723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6922729 : List Nat := [1, 2, 1, 1, 1, 2, 1, 9, 1, 1, 3]
def baseStart_6922729 : Nat := 118140960795 + 6922729 * 2 ^ 59
def prefixEnd_6922729 : Nat := 4983230072969 + 3 ^ 40 * 6922729 * 2
def baseEnd_6922729 : Nat := 3554687417819150524650455

theorem tailTrace_6922729 : CollatzResearch.WordTrace tailWord_6922729 prefixEnd_6922729 3554687417819150524650455 := by
  unfold tailWord_6922729
  simp only [CollatzResearch.WordTrace]
  refine ⟨252492669737142615829963241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168328446491428410553308827 252492669737142615829963241)
  ·
    refine ⟨189369502302856961872472431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252492669737142615829963241 189369502302856961872472431)
    ·
      refine ⟨284054253454285442808708647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189369502302856961872472431 284054253454285442808708647)
      ·
        refine ⟨426081380181428164213062971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284054253454285442808708647 426081380181428164213062971)
        ·
          refine ⟨639122070272142246319594457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426081380181428164213062971 639122070272142246319594457)
          ·
            refine ⟨479341552704106684739695843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 639122070272142246319594457 479341552704106684739695843)
            ·
              refine ⟨719012329056160027109543765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 479341552704106684739695843 719012329056160027109543765)
              ·
                refine ⟨4212962865563437658844983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 719012329056160027109543765 4212962865563437658844983)
                ·
                  refine ⟨6319444298345156488267475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4212962865563437658844983 6319444298345156488267475)
                  ·
                    refine ⟨9479166447517734732401213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6319444298345156488267475 9479166447517734732401213)
                    ·
                      refine ⟨3554687417819150524650455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9479166447517734732401213 3554687417819150524650455)
                      ·
                        rfl

theorem cell23_6922729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 9, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 9, 1, 1, 3].length) (baseStart_6922729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6922729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6922729 prefixEnd_6922729 := by exact prefixLift 6922729
  have htrace : WordTrace (prefixWord ++ tailWord_6922729) baseStart_6922729 baseEnd_6922729 := by
    simpa [prefixWord, tailWord_6922729, baseEnd_6922729] using wordTrace_append hprefix tailTrace_6922729
  have hstable : (prefixWord ++ tailWord_6922729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6922729).length < 2 ^ (prefixWord ++ tailWord_6922729).sum := by decide
  have hdescent : baseEnd_6922729 < baseStart_6922729 := by decide
  rcases family_descends (prefixWord ++ tailWord_6922729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6922735 : List Nat := [1, 1, 2, 1, 4, 1, 1, 2, 5, 1, 4]
def baseStart_6922735 : Nat := 118140960795 + 6922735 * 2 ^ 59
def prefixEnd_6922735 : Nat := 4983230072969 + 3 ^ 40 * 6922735 * 2
def baseEnd_6922735 : Nat := 3554690498703077501175427

theorem tailTrace_6922735 : CollatzResearch.WordTrace tailWord_6922735 prefixEnd_6922735 3554690498703077501175427 := by
  unfold tailWord_6922735
  simp only [CollatzResearch.WordTrace]
  refine ⟨252492888575120878854681659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168328592383413919236454439 252492888575120878854681659)
  ·
    refine ⟨378739332862681318282022489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252492888575120878854681659 378739332862681318282022489)
    ·
      refine ⟨284054499647010988711516867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 378739332862681318282022489 284054499647010988711516867)
      ·
        refine ⟨426081749470516483067275301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284054499647010988711516867 426081749470516483067275301)
        ·
          refine ⟨79890328025721840575114119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 426081749470516483067275301 79890328025721840575114119)
          ·
            refine ⟨119835492038582760862671179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79890328025721840575114119 119835492038582760862671179)
            ·
              refine ⟨179753238057874141294006769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119835492038582760862671179 179753238057874141294006769)
              ·
                refine ⟨134814928543405605970505077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179753238057874141294006769 134814928543405605970505077)
                ·
                  refine ⟨12638899550944275559734851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 134814928543405605970505077 12638899550944275559734851)
                  ·
                    refine ⟨18958349326416413339602277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12638899550944275559734851 18958349326416413339602277)
                    ·
                      refine ⟨3554690498703077501175427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18958349326416413339602277 3554690498703077501175427)
                      ·
                        rfl

theorem cell23_6922735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 5, 1, 4].length) (baseStart_6922735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6922735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6922735 prefixEnd_6922735 := by exact prefixLift 6922735
  have htrace : WordTrace (prefixWord ++ tailWord_6922735) baseStart_6922735 baseEnd_6922735 := by
    simpa [prefixWord, tailWord_6922735, baseEnd_6922735] using wordTrace_append hprefix tailTrace_6922735
  have hstable : (prefixWord ++ tailWord_6922735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6922735).length < 2 ^ (prefixWord ++ tailWord_6922735).sum := by decide
  have hdescent : baseEnd_6922735 < baseStart_6922735 := by decide
  rcases family_descends (prefixWord ++ tailWord_6922735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6922755 : List Nat := [1, 1, 1, 3, 2, 1, 3, 4, 1, 1, 5]
def baseStart_6922755 : Nat := 118140960795 + 6922755 * 2 ^ 59
def prefixEnd_6922755 : Nat := 4983230072969 + 3 ^ 40 * 6922755 * 2
def baseEnd_6922755 : Nat := 3554700768316167422925335

theorem tailTrace_6922755 : CollatzResearch.WordTrace tailWord_6922755 prefixEnd_6922755 3554700768316167422925335 := by
  unfold tailWord_6922755
  simp only [CollatzResearch.WordTrace]
  refine ⟨252493618035048422270409719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168329078690032281513606479 252493618035048422270409719)
  ·
    refine ⟨378740427052572633405614579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252493618035048422270409719 378740427052572633405614579)
    ·
      refine ⟨568110640578858950108421869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378740427052572633405614579 568110640578858950108421869)
      ·
        refine ⟨213041490217072106290658201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 568110640578858950108421869 213041490217072106290658201)
        ·
          refine ⟨159781117662804079717993651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213041490217072106290658201 159781117662804079717993651)
          ·
            refine ⟨239671676494206119576990477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159781117662804079717993651 239671676494206119576990477)
            ·
              refine ⟨89876878685327294841371429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 239671676494206119576990477 89876878685327294841371429)
              ·
                refine ⟨16851914753498867782757143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89876878685327294841371429 16851914753498867782757143)
                ·
                  refine ⟨25277872130248301674135715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16851914753498867782757143 25277872130248301674135715)
                  ·
                    refine ⟨37916808195372452511203573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25277872130248301674135715 37916808195372452511203573)
                    ·
                      refine ⟨3554700768316167422925335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37916808195372452511203573 3554700768316167422925335)
                      ·
                        rfl

theorem cell23_6922755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 4, 1, 1, 5].length) (baseStart_6922755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6922755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6922755 prefixEnd_6922755 := by exact prefixLift 6922755
  have htrace : WordTrace (prefixWord ++ tailWord_6922755) baseStart_6922755 baseEnd_6922755 := by
    simpa [prefixWord, tailWord_6922755, baseEnd_6922755] using wordTrace_append hprefix tailTrace_6922755
  have hstable : (prefixWord ++ tailWord_6922755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6922755).length < 2 ^ (prefixWord ++ tailWord_6922755).sum := by decide
  have hdescent : baseEnd_6922755 < baseStart_6922755 := by decide
  rcases family_descends (prefixWord ++ tailWord_6922755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6922797 : List Nat := [1, 5, 4, 1, 1, 1, 1, 4, 1, 1, 3]
def baseStart_6922797 : Nat := 118140960795 + 6922797 * 2 ^ 59
def prefixEnd_6922797 : Nat := 4983230072969 + 3 ^ 40 * 6922797 * 2
def baseEnd_6922797 : Nat := 3554722334503656258600143

theorem tailTrace_6922797 : CollatzResearch.WordTrace tailWord_6922797 prefixEnd_6922797 3554722334503656258600143 := by
  unfold tailWord_6922797
  simp only [CollatzResearch.WordTrace]
  refine ⟨252495149900896263443438645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168330099933930842295625763 252495149900896263443438645)
  ·
    refine ⟨23671420303209024697822373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 252495149900896263443438645 23671420303209024697822373)
    ·
      refine ⟨4438391306851692130841695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23671420303209024697822373 4438391306851692130841695)
      ·
        refine ⟨6657586960277538196262543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4438391306851692130841695 6657586960277538196262543)
        ·
          refine ⟨9986380440416307294393815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6657586960277538196262543 9986380440416307294393815)
          ·
            refine ⟨14979570660624460941590723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9986380440416307294393815 14979570660624460941590723)
            ·
              refine ⟨22469355990936691412386085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14979570660624460941590723 22469355990936691412386085)
              ·
                refine ⟨4213004248300629639822391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22469355990936691412386085 4213004248300629639822391)
                ·
                  refine ⟨6319506372450944459733587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4213004248300629639822391 6319506372450944459733587)
                  ·
                    refine ⟨9479259558676416689600381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6319506372450944459733587 9479259558676416689600381)
                    ·
                      refine ⟨3554722334503656258600143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9479259558676416689600381 3554722334503656258600143)
                      ·
                        rfl

theorem cell23_6922797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_6922797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6922797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6922797 prefixEnd_6922797 := by exact prefixLift 6922797
  have htrace : WordTrace (prefixWord ++ tailWord_6922797) baseStart_6922797 baseEnd_6922797 := by
    simpa [prefixWord, tailWord_6922797, baseEnd_6922797] using wordTrace_append hprefix tailTrace_6922797
  have hstable : (prefixWord ++ tailWord_6922797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6922797).length < 2 ^ (prefixWord ++ tailWord_6922797).sum := by decide
  have hdescent : baseEnd_6922797 < baseStart_6922797 := by decide
  rcases family_descends (prefixWord ++ tailWord_6922797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6922805 : List Nat := [1, 3, 3, 1, 1, 2, 1, 1, 1, 9]
def baseStart_6922805 : Nat := 118140960795 + 6922805 * 2 ^ 59
def prefixEnd_6922805 : Nat := 4983230072969 + 3 ^ 40 * 6922805 * 2
def baseEnd_6922805 : Nat := 1184908814116297409100035

theorem tailTrace_6922805 : CollatzResearch.WordTrace tailWord_6922805 prefixEnd_6922805 1184908814116297409100035 := by
  unfold tailWord_6922805
  simp only [CollatzResearch.WordTrace]
  refine ⟨252495441684867280809729869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168330294456578187206486579 252495441684867280809729869)
  ·
    refine ⟨94685790631825230303648701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252495441684867280809729869 94685790631825230303648701)
    ·
      refine ⟨35507171486934461363868263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94685790631825230303648701 35507171486934461363868263)
      ·
        refine ⟨53260757230401692045802395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35507171486934461363868263 53260757230401692045802395)
        ·
          refine ⟨79891135845602538068703593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53260757230401692045802395 79891135845602538068703593)
          ·
            refine ⟨59918351884201903551527695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79891135845602538068703593 59918351884201903551527695)
            ·
              refine ⟨89877527826302855327291543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59918351884201903551527695 89877527826302855327291543)
              ·
                refine ⟨134816291739454282990937315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89877527826302855327291543 134816291739454282990937315)
                ·
                  refine ⟨202224437609181424486405973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134816291739454282990937315 202224437609181424486405973)
                  ·
                    refine ⟨1184908814116297409100035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 202224437609181424486405973 1184908814116297409100035)
                    ·
                      rfl

theorem cell23_6922805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_6922805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6922805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6922805 prefixEnd_6922805 := by exact prefixLift 6922805
  have htrace : WordTrace (prefixWord ++ tailWord_6922805) baseStart_6922805 baseEnd_6922805 := by
    simpa [prefixWord, tailWord_6922805, baseEnd_6922805] using wordTrace_append hprefix tailTrace_6922805
  have hstable : (prefixWord ++ tailWord_6922805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6922805).length < 2 ^ (prefixWord ++ tailWord_6922805).sum := by decide
  have hdescent : baseEnd_6922805 < baseStart_6922805 := by decide
  rcases family_descends (prefixWord ++ tailWord_6922805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6922853 : List Nat := [1, 3, 1, 3, 4, 2, 1, 2, 2, 1, 3]
def baseStart_6922853 : Nat := 118140960795 + 6922853 * 2 ^ 59
def prefixEnd_6922853 : Nat := 4983230072969 + 3 ^ 40 * 6922853 * 2
def baseEnd_6922853 : Nat := 3554751089420308039499885

theorem tailTrace_6922853 : CollatzResearch.WordTrace tailWord_6922853 prefixEnd_6922853 3554751089420308039499885 := by
  unfold tailWord_6922853
  simp only [CollatzResearch.WordTrace]
  refine ⟨252497192388693385007477213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168331461592462256671651475 252497192388693385007477213)
  ·
    refine ⟨94686447145760019377803955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252497192388693385007477213 94686447145760019377803955)
    ·
      refine ⟨142029670718640029066705933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94686447145760019377803955 142029670718640029066705933)
      ·
        refine ⟨53261126519490010900014725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142029670718640029066705933 53261126519490010900014725)
        ·
          refine ⟨9986461222404377043752761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53261126519490010900014725 9986461222404377043752761)
          ·
            refine ⟨7489845916803282782814571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9986461222404377043752761 7489845916803282782814571)
            ·
              refine ⟨11234768875204924174221857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7489845916803282782814571 11234768875204924174221857)
              ·
                refine ⟨8426076656403693130666393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11234768875204924174221857 8426076656403693130666393)
                ·
                  refine ⟨6319557492302769847999795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8426076656403693130666393 6319557492302769847999795)
                  ·
                    refine ⟨9479336238454154771999693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6319557492302769847999795 9479336238454154771999693)
                    ·
                      refine ⟨3554751089420308039499885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9479336238454154771999693 3554751089420308039499885)
                      ·
                        rfl

theorem cell23_6922853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 2, 2, 1, 3].length) (baseStart_6922853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6922853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6922853 prefixEnd_6922853 := by exact prefixLift 6922853
  have htrace : WordTrace (prefixWord ++ tailWord_6922853) baseStart_6922853 baseEnd_6922853 := by
    simpa [prefixWord, tailWord_6922853, baseEnd_6922853] using wordTrace_append hprefix tailTrace_6922853
  have hstable : (prefixWord ++ tailWord_6922853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6922853).length < 2 ^ (prefixWord ++ tailWord_6922853).sum := by decide
  have hdescent : baseEnd_6922853 < baseStart_6922853 := by decide
  rcases family_descends (prefixWord ++ tailWord_6922853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6922870 : List Nat := [5, 1, 1, 2, 3, 1, 3, 1, 2, 1, 3]
def baseStart_6922870 : Nat := 118140960795 + 6922870 * 2 ^ 59
def prefixEnd_6922870 : Nat := 4983230072969 + 3 ^ 40 * 6922870 * 2
def baseEnd_6922870 : Nat := 3554759818591434472987307

theorem tailTrace_6922870 : CollatzResearch.WordTrace tailWord_6922870 prefixEnd_6922870 3554759818591434472987307 := by
  unfold tailWord_6922870
  simp only [CollatzResearch.WordTrace]
  refine ⟨15781113276851987306927879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 168331874953087864607230709 15781113276851987306927879)
  ·
    refine ⟨23671669915277980960391819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15781113276851987306927879 23671669915277980960391819)
    ·
      refine ⟨35507504872916971440587729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23671669915277980960391819 35507504872916971440587729)
      ·
        refine ⟨26630628654687728580440797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35507504872916971440587729 26630628654687728580440797)
        ·
          refine ⟨9986485745507898217665299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26630628654687728580440797 9986485745507898217665299)
          ·
            refine ⟨14979728618261847326497949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9986485745507898217665299 14979728618261847326497949)
            ·
              refine ⟨5617398231848192747436731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14979728618261847326497949 5617398231848192747436731)
              ·
                refine ⟨8426097347772289121155097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5617398231848192747436731 8426097347772289121155097)
                ·
                  refine ⟨6319573010829216840866323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8426097347772289121155097 6319573010829216840866323)
                  ·
                    refine ⟨9479359516243825261299485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6319573010829216840866323 9479359516243825261299485)
                    ·
                      refine ⟨3554759818591434472987307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9479359516243825261299485 3554759818591434472987307)
                      ·
                        rfl

theorem cell23_6922870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 3, 1, 2, 1, 3].length) (baseStart_6922870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6922870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6922870 prefixEnd_6922870 := by exact prefixLift 6922870
  have htrace : WordTrace (prefixWord ++ tailWord_6922870) baseStart_6922870 baseEnd_6922870 := by
    simpa [prefixWord, tailWord_6922870, baseEnd_6922870] using wordTrace_append hprefix tailTrace_6922870
  have hstable : (prefixWord ++ tailWord_6922870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6922870).length < 2 ^ (prefixWord ++ tailWord_6922870).sum := by decide
  have hdescent : baseEnd_6922870 < baseStart_6922870 := by decide
  rcases family_descends (prefixWord ++ tailWord_6922870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6922876 : List Nat := [2, 2, 2, 1, 1, 2, 2, 5, 2, 2, 2]
def baseStart_6922876 : Nat := 118140960795 + 6922876 * 2 ^ 59
def prefixEnd_6922876 : Nat := 4983230072969 + 3 ^ 40 * 6922876 * 2
def baseEnd_6922876 : Nat := 3554762899475361449512279

theorem tailTrace_6922876 : CollatzResearch.WordTrace tailWord_6922876 prefixEnd_6922876 3554762899475361449512279 := by
  unfold tailWord_6922876
  simp only [CollatzResearch.WordTrace]
  refine ⟨126249015633805029967782241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168332020845073373290376321 126249015633805029967782241)
  ·
    refine ⟨94686761725353772475836681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126249015633805029967782241 94686761725353772475836681)
    ·
      refine ⟨71015071294015329356877511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94686761725353772475836681 71015071294015329356877511)
      ·
        refine ⟨106522606941022994035316267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71015071294015329356877511 106522606941022994035316267)
        ·
          refine ⟨159783910411534491052974401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106522606941022994035316267 159783910411534491052974401)
          ·
            refine ⟨119837932808650868289730801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159783910411534491052974401 119837932808650868289730801)
            ·
              refine ⟨89878449606488151217298101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119837932808650868289730801 89878449606488151217298101)
              ·
                refine ⟨8426104650608264176621697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89878449606488151217298101 8426104650608264176621697)
                ·
                  refine ⟨6319578487956198132466273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8426104650608264176621697 6319578487956198132466273)
                  ·
                    refine ⟨4739683865967148599349705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6319578487956198132466273 4739683865967148599349705)
                    ·
                      refine ⟨3554762899475361449512279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4739683865967148599349705 3554762899475361449512279)
                      ·
                        rfl

theorem cell23_6922876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 5, 2, 2, 2].length) (baseStart_6922876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6922876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6922876 prefixEnd_6922876 := by exact prefixLift 6922876
  have htrace : WordTrace (prefixWord ++ tailWord_6922876) baseStart_6922876 baseEnd_6922876 := by
    simpa [prefixWord, tailWord_6922876, baseEnd_6922876] using wordTrace_append hprefix tailTrace_6922876
  have hstable : (prefixWord ++ tailWord_6922876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6922876).length < 2 ^ (prefixWord ++ tailWord_6922876).sum := by decide
  have hdescent : baseEnd_6922876 < baseStart_6922876 := by decide
  rcases family_descends (prefixWord ++ tailWord_6922876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6922892 : List Nat := [2, 2, 1, 2, 1, 1, 2, 2, 4, 3, 3]
def baseStart_6922892 : Nat := 118140960795 + 6922892 * 2 ^ 59
def prefixEnd_6922892 : Nat := 4983230072969 + 3 ^ 40 * 6922892 * 2
def baseEnd_6922892 : Nat := 3554771115165833386912205

theorem tailTrace_6922892 : CollatzResearch.WordTrace tailWord_6922892 prefixEnd_6922892 3554771115165833386912205 := by
  unfold tailWord_6922892
  simp only [CollatzResearch.WordTrace]
  refine ⟨126249307417776047334073465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168332409890368063112097953 126249307417776047334073465)
  ·
    refine ⟨94686980563332035500555099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126249307417776047334073465 94686980563332035500555099)
    ·
      refine ⟨142030470844998053250832649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94686980563332035500555099 142030470844998053250832649)
      ·
        refine ⟨106522853133748539938124487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142030470844998053250832649 106522853133748539938124487)
        ·
          refine ⟨159784279700622809907186731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106522853133748539938124487 159784279700622809907186731)
          ·
            refine ⟨239676419550934214860780097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159784279700622809907186731 239676419550934214860780097)
            ·
              refine ⟨179757314663200661145585073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 239676419550934214860780097 179757314663200661145585073)
              ·
                refine ⟨134817985997400495859188805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179757314663200661145585073 134817985997400495859188805)
                ·
                  refine ⟨25278372374512592973597901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 134817985997400495859188805 25278372374512592973597901)
                  ·
                    refine ⟨9479389640442222365099213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25278372374512592973597901 9479389640442222365099213)
                    ·
                      refine ⟨3554771115165833386912205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9479389640442222365099213 3554771115165833386912205)
                      ·
                        rfl

theorem cell23_6922892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 4, 3, 3].length) (baseStart_6922892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6922892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6922892 prefixEnd_6922892 := by exact prefixLift 6922892
  have htrace : WordTrace (prefixWord ++ tailWord_6922892) baseStart_6922892 baseEnd_6922892 := by
    simpa [prefixWord, tailWord_6922892, baseEnd_6922892] using wordTrace_append hprefix tailTrace_6922892
  have hstable : (prefixWord ++ tailWord_6922892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6922892).length < 2 ^ (prefixWord ++ tailWord_6922892).sum := by decide
  have hdescent : baseEnd_6922892 < baseStart_6922892 := by decide
  rcases family_descends (prefixWord ++ tailWord_6922892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6922916 : List Nat := [2, 3, 1, 2, 2, 1, 5, 2, 5]
def baseStart_6922916 : Nat := 118140960795 + 6922916 * 2 ^ 59
def prefixEnd_6922916 : Nat := 4983230072969 + 3 ^ 40 * 6922916 * 2
def baseEnd_6922916 : Nat := 394975937633504588112455

theorem tailTrace_6922916 : CollatzResearch.WordTrace tailWord_6922916 prefixEnd_6922916 394975937633504588112455 := by
  unfold tailWord_6922916
  simp only [CollatzResearch.WordTrace]
  refine ⟨126249745093732573383510301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168332993458310097844680401 126249745093732573383510301)
  ·
    refine ⟨47343654410149715018816363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126249745093732573383510301 47343654410149715018816363)
    ·
      refine ⟨71015481615224572528224545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47343654410149715018816363 71015481615224572528224545)
      ·
        refine ⟨53261611211418429396168409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71015481615224572528224545 53261611211418429396168409)
        ·
          refine ⟨39946208408563822047126307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53261611211418429396168409 39946208408563822047126307)
          ·
            refine ⟨59919312612845733070689461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39946208408563822047126307 59919312612845733070689461)
            ·
              refine ⟨5617435557454287475377137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59919312612845733070689461 5617435557454287475377137)
              ·
                refine ⟨4213076668090715606532853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5617435557454287475377137 4213076668090715606532853)
                ·
                  refine ⟨394975937633504588112455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4213076668090715606532853 394975937633504588112455)
                  ·
                    rfl

theorem cell23_6922916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 5, 2, 5].length) (baseStart_6922916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6922916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6922916 prefixEnd_6922916 := by exact prefixLift 6922916
  have htrace : WordTrace (prefixWord ++ tailWord_6922916) baseStart_6922916 baseEnd_6922916 := by
    simpa [prefixWord, tailWord_6922916, baseEnd_6922916] using wordTrace_append hprefix tailTrace_6922916
  have hstable : (prefixWord ++ tailWord_6922916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6922916).length < 2 ^ (prefixWord ++ tailWord_6922916).sum := by decide
  have hdescent : baseEnd_6922916 < baseStart_6922916 := by decide
  rcases family_descends (prefixWord ++ tailWord_6922916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6922969 : List Nat := [1, 2, 1, 2, 3, 2, 1, 4, 2, 2, 3]
def baseStart_6922969 : Nat := 118140960795 + 6922969 * 2 ^ 59
def prefixEnd_6922969 : Nat := 4983230072969 + 3 ^ 40 * 6922969 * 2
def baseEnd_6922969 : Nat := 3554810653176229585649351

theorem tailTrace_6922969 : CollatzResearch.WordTrace tailWord_6922969 prefixEnd_6922969 3554810653176229585649351 := by
  unfold tailWord_6922969
  simp only [CollatzResearch.WordTrace]
  refine ⟨252501423256273136818699961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168334282170848757879133307 252501423256273136818699961)
  ·
    refine ⟨189376067442204852614024971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252501423256273136818699961 189376067442204852614024971)
    ·
      refine ⟨284064101163307278921037457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189376067442204852614024971 284064101163307278921037457)
      ·
        refine ⟨213048075872480459190778093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 284064101163307278921037457 213048075872480459190778093)
        ·
          refine ⟨79893028452180172196541785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 213048075872480459190778093 79893028452180172196541785)
          ·
            refine ⟨59919771339135129147406339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79893028452180172196541785 59919771339135129147406339)
            ·
              refine ⟨89879657008702693721109509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59919771339135129147406339 89879657008702693721109509)
              ·
                refine ⟨16852435689131755072708033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89879657008702693721109509 16852435689131755072708033)
                ·
                  refine ⟨12639326766848816304531025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16852435689131755072708033 12639326766848816304531025)
                  ·
                    refine ⟨9479495075136612228398269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12639326766848816304531025 9479495075136612228398269)
                    ·
                      refine ⟨3554810653176229585649351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9479495075136612228398269 3554810653176229585649351)
                      ·
                        rfl

theorem cell23_6922969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 4, 2, 2, 3].length) (baseStart_6922969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6922969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6922969 prefixEnd_6922969 := by exact prefixLift 6922969
  have htrace : WordTrace (prefixWord ++ tailWord_6922969) baseStart_6922969 baseEnd_6922969 := by
    simpa [prefixWord, tailWord_6922969, baseEnd_6922969] using wordTrace_append hprefix tailTrace_6922969
  have hstable : (prefixWord ++ tailWord_6922969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6922969).length < 2 ^ (prefixWord ++ tailWord_6922969).sum := by decide
  have hdescent : baseEnd_6922969 < baseStart_6922969 := by decide
  rcases family_descends (prefixWord ++ tailWord_6922969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6922989 : List Nat := [1, 5, 1, 2, 1, 1, 1, 5, 6]
def baseStart_6922989 : Nat := 118140960795 + 6922989 * 2 ^ 59
def prefixEnd_6922989 : Nat := 4983230072969 + 3 ^ 40 * 6922989 * 2
def baseEnd_6922989 : Nat := 394980102532146611933251

theorem tailTrace_6922989 : CollatzResearch.WordTrace tailWord_6922989 prefixEnd_6922989 394980102532146611933251 := by
  unfold tailWord_6922989
  simp only [CollatzResearch.WordTrace]
  refine ⟨252502152716200680234428021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168334768477467120156285347 252502152716200680234428021)
  ·
    refine ⟨23672076817143813771977627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 252502152716200680234428021 23672076817143813771977627)
    ·
      refine ⟨35508115225715720657966441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23672076817143813771977627 35508115225715720657966441)
      ·
        refine ⟨26631086419286790493474831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35508115225715720657966441 26631086419286790493474831)
        ·
          refine ⟨39946629628930185740212247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26631086419286790493474831 39946629628930185740212247)
          ·
            refine ⟨59919944443395278610318371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39946629628930185740212247 59919944443395278610318371)
            ·
              refine ⟨89879916665092917915477557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59919944443395278610318371 89879916665092917915477557)
              ·
                refine ⟨8426242187352461054576021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89879916665092917915477557 8426242187352461054576021)
                ·
                  refine ⟨394980102532146611933251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8426242187352461054576021 394980102532146611933251)
                  ·
                    rfl

theorem cell23_6922989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 5, 6].length) (baseStart_6922989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6922989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6922989 prefixEnd_6922989 := by exact prefixLift 6922989
  have htrace : WordTrace (prefixWord ++ tailWord_6922989) baseStart_6922989 baseEnd_6922989 := by
    simpa [prefixWord, tailWord_6922989, baseEnd_6922989] using wordTrace_append hprefix tailTrace_6922989
  have hstable : (prefixWord ++ tailWord_6922989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6922989).length < 2 ^ (prefixWord ++ tailWord_6922989).sum := by decide
  have hdescent : baseEnd_6922989 < baseStart_6922989 := by decide
  rcases family_descends (prefixWord ++ tailWord_6922989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6922997 : List Nat := [1, 3, 6, 1, 2, 1, 1, 1, 2, 5]
def baseStart_6922997 : Nat := 118140960795 + 6922997 * 2 ^ 59
def prefixEnd_6922997 : Nat := 4983230072969 + 3 ^ 40 * 6922997 * 2
def baseEnd_6922997 : Nat := 1184941676878185158699741

theorem tailTrace_6922997 : CollatzResearch.WordTrace tailWord_6922997 prefixEnd_6922997 1184941676878185158699741 := by
  unfold tailWord_6922997
  simp only [CollatzResearch.WordTrace]
  refine ⟨252502444500171697600719245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168334963000114465067146163 252502444500171697600719245)
  ·
    refine ⟨94688416687564386600269717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252502444500171697600719245 94688416687564386600269717)
    ·
      refine ⟨4438519532229580621887643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 94688416687564386600269717 4438519532229580621887643)
      ·
        refine ⟨6657779298344370932831465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4438519532229580621887643 6657779298344370932831465)
        ·
          refine ⟨4993334473758278199623599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6657779298344370932831465 4993334473758278199623599)
          ·
            refine ⟨7490001710637417299435399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4993334473758278199623599 7490001710637417299435399)
            ·
              refine ⟨11235002565956125949153099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7490001710637417299435399 11235002565956125949153099)
              ·
                refine ⟨16852503848934188923729649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11235002565956125949153099 16852503848934188923729649)
                ·
                  refine ⟨12639377886700641692797237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16852503848934188923729649 12639377886700641692797237)
                  ·
                    refine ⟨1184941676878185158699741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12639377886700641692797237 1184941676878185158699741)
                    ·
                      rfl

theorem cell23_6922997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_6922997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6922997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6922997 prefixEnd_6922997 := by exact prefixLift 6922997
  have htrace : WordTrace (prefixWord ++ tailWord_6922997) baseStart_6922997 baseEnd_6922997 := by
    simpa [prefixWord, tailWord_6922997, baseEnd_6922997] using wordTrace_append hprefix tailTrace_6922997
  have hstable : (prefixWord ++ tailWord_6922997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6922997).length < 2 ^ (prefixWord ++ tailWord_6922997).sum := by decide
  have hdescent : baseEnd_6922997 < baseStart_6922997 := by decide
  rcases family_descends (prefixWord ++ tailWord_6922997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6923010 : List Nat := [3, 4, 1, 1, 1, 3, 2, 3, 1, 4]
def baseStart_6923010 : Nat := 118140960795 + 6923010 * 2 ^ 59
def prefixEnd_6923010 : Nat := 4983230072969 + 3 ^ 40 * 6923010 * 2
def baseEnd_6923010 : Nat := 1184943901961021308412221

theorem tailTrace_6923010 : CollatzResearch.WordTrace tailWord_6923010 prefixEnd_6923010 1184943901961021308412221 := by
  unfold tailWord_6923010
  simp only [CollatzResearch.WordTrace]
  refine ⟨63125729662281150205235621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168335279099416400547294989 63125729662281150205235621)
  ·
    refine ⟨11836074311677715663481679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63125729662281150205235621 11836074311677715663481679)
    ·
      refine ⟨17754111467516573495222519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11836074311677715663481679 17754111467516573495222519)
      ·
        refine ⟨26631167201274860242833779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17754111467516573495222519 26631167201274860242833779)
        ·
          refine ⟨39946750801912290364250669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26631167201274860242833779 39946750801912290364250669)
          ·
            refine ⟨14980031550717108886594001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39946750801912290364250669 14980031550717108886594001)
            ·
              refine ⟨11235023663037831664945501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14980031550717108886594001 11235023663037831664945501)
              ·
                refine ⟨4213133873639186874354563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11235023663037831664945501 4213133873639186874354563)
                ·
                  refine ⟨6319700810458780311531845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4213133873639186874354563 6319700810458780311531845)
                  ·
                    refine ⟨1184943901961021308412221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6319700810458780311531845 1184943901961021308412221)
                    ·
                      rfl

theorem cell23_6923010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_6923010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6923010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6923010 prefixEnd_6923010 := by exact prefixLift 6923010
  have htrace : WordTrace (prefixWord ++ tailWord_6923010) baseStart_6923010 baseEnd_6923010 := by
    simpa [prefixWord, tailWord_6923010, baseEnd_6923010] using wordTrace_append hprefix tailTrace_6923010
  have hstable : (prefixWord ++ tailWord_6923010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6923010).length < 2 ^ (prefixWord ++ tailWord_6923010).sum := by decide
  have hdescent : baseEnd_6923010 < baseStart_6923010 := by decide
  rcases family_descends (prefixWord ++ tailWord_6923010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6923100 : List Nat := [2, 2, 4, 2, 1, 1, 4, 1, 2, 4]
def baseStart_6923100 : Nat := 118140960795 + 6923100 * 2 ^ 59
def prefixEnd_6923100 : Nat := 4983230072969 + 3 ^ 40 * 6923100 * 2
def baseEnd_6923100 : Nat := 1184959306380656191037083

theorem tailTrace_6923100 : CollatzResearch.WordTrace tailWord_6923100 prefixEnd_6923100 1184959306380656191037083 := by
  unfold tailWord_6923100
  simp only [CollatzResearch.WordTrace]
  refine ⟨126253100609399273095859377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168337467479199030794479169 126253100609399273095859377)
  ·
    refine ⟨94689825457049454821894533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126253100609399273095859377 94689825457049454821894533)
    ·
      refine ⟨17754342273196772779105225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94689825457049454821894533 17754342273196772779105225)
      ·
        refine ⟨13315756704897579584328919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17754342273196772779105225 13315756704897579584328919)
        ·
          refine ⟨19973635057346369376493379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13315756704897579584328919 19973635057346369376493379)
          ·
            refine ⟨29960452586019554064740069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19973635057346369376493379 29960452586019554064740069)
            ·
              refine ⟨5617584859878666387138763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29960452586019554064740069 5617584859878666387138763)
              ·
                refine ⟨8426377289817999580708145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5617584859878666387138763 8426377289817999580708145)
                ·
                  refine ⟨6319782967363499685531109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8426377289817999580708145 6319782967363499685531109)
                  ·
                    refine ⟨1184959306380656191037083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6319782967363499685531109 1184959306380656191037083)
                    ·
                      rfl

theorem cell23_6923100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_6923100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6923100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6923100 prefixEnd_6923100 := by exact prefixLift 6923100
  have htrace : WordTrace (prefixWord ++ tailWord_6923100) baseStart_6923100 baseEnd_6923100 := by
    simpa [prefixWord, tailWord_6923100, baseEnd_6923100] using wordTrace_append hprefix tailTrace_6923100
  have hstable : (prefixWord ++ tailWord_6923100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6923100).length < 2 ^ (prefixWord ++ tailWord_6923100).sum := by decide
  have hdescent : baseEnd_6923100 < baseStart_6923100 := by decide
  rcases family_descends (prefixWord ++ tailWord_6923100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6923133 : List Nat := [1, 4, 1, 1, 2, 1, 2, 5, 1, 3, 2]
def baseStart_6923133 : Nat := 118140960795 + 6923133 * 2 ^ 59
def prefixEnd_6923133 : Nat := 4983230072969 + 3 ^ 40 * 6923133 * 2
def baseEnd_6923133 : Nat := 3554894864003566943998597

theorem tailTrace_6923133 : CollatzResearch.WordTrace tailWord_6923133 prefixEnd_6923133 3554894864003566943998597 := by
  unfold tailWord_6923133
  simp only [CollatzResearch.WordTrace]
  refine ⟨252507404827678992827670053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168338269885119328551780035 252507404827678992827670053)
  ·
    refine ⟨47345138405189811155188135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 252507404827678992827670053 47345138405189811155188135)
    ·
      refine ⟨71017707607784716732782203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47345138405189811155188135 71017707607784716732782203)
      ·
        refine ⟨106526561411677075099173305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71017707607784716732782203 106526561411677075099173305)
        ·
          refine ⟨79894921058757806324379979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106526561411677075099173305 79894921058757806324379979)
          ·
            refine ⟨119842381588136709486569969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79894921058757806324379979 119842381588136709486569969)
            ·
              refine ⟨89881786191102532114927477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119842381588136709486569969 89881786191102532114927477)
              ·
                refine ⟨8426417455415862385774451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89881786191102532114927477 8426417455415862385774451)
                ·
                  refine ⟨12639626183123793578661677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8426417455415862385774451 12639626183123793578661677)
                  ·
                    refine ⟨4739859818671422591998129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12639626183123793578661677 4739859818671422591998129)
                    ·
                      refine ⟨3554894864003566943998597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4739859818671422591998129 3554894864003566943998597)
                      ·
                        rfl

theorem cell23_6923133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 5, 1, 3, 2].length) (baseStart_6923133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6923133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6923133 prefixEnd_6923133 := by exact prefixLift 6923133
  have htrace : WordTrace (prefixWord ++ tailWord_6923133) baseStart_6923133 baseEnd_6923133 := by
    simpa [prefixWord, tailWord_6923133, baseEnd_6923133] using wordTrace_append hprefix tailTrace_6923133
  have hstable : (prefixWord ++ tailWord_6923133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6923133).length < 2 ^ (prefixWord ++ tailWord_6923133).sum := by decide
  have hdescent : baseEnd_6923133 < baseStart_6923133 := by decide
  rcases family_descends (prefixWord ++ tailWord_6923133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6923139 : List Nat := [1, 1, 1, 3, 4, 1, 2, 2, 2, 6]
def baseStart_6923139 : Nat := 118140960795 + 6923139 * 2 ^ 59
def prefixEnd_6923139 : Nat := 4983230072969 + 3 ^ 40 * 6923139 * 2
def baseEnd_6923139 : Nat := 1184965981629164640174523

theorem tailTrace_6923139 : CollatzResearch.WordTrace tailWord_6923139 prefixEnd_6923139 1184965981629164640174523 := by
  unfold tailWord_6923139
  simp only [CollatzResearch.WordTrace]
  refine ⟨252507623665657255852388471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168338415777104837234925647 252507623665657255852388471)
  ·
    refine ⟨378761435498485883778582707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252507623665657255852388471 378761435498485883778582707)
    ·
      refine ⟨568142153247728825667874061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378761435498485883778582707 568142153247728825667874061)
      ·
        refine ⟨213053307467898309625452773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 568142153247728825667874061 213053307467898309625452773)
        ·
          refine ⟨39947495150230933054772395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 213053307467898309625452773 39947495150230933054772395)
          ·
            refine ⟨59921242725346399582158593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39947495150230933054772395 59921242725346399582158593)
            ·
              refine ⟨44940932044009799686618945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59921242725346399582158593 44940932044009799686618945)
              ·
                refine ⟨33705699033007349764964209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44940932044009799686618945 33705699033007349764964209)
                ·
                  refine ⟨25279274274755512323723157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33705699033007349764964209 25279274274755512323723157)
                  ·
                    refine ⟨1184965981629164640174523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25279274274755512323723157 1184965981629164640174523)
                    ·
                      rfl

theorem cell23_6923139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 2, 6].length) (baseStart_6923139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6923139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6923139 prefixEnd_6923139 := by exact prefixLift 6923139
  have htrace : WordTrace (prefixWord ++ tailWord_6923139) baseStart_6923139 baseEnd_6923139 := by
    simpa [prefixWord, tailWord_6923139, baseEnd_6923139] using wordTrace_append hprefix tailTrace_6923139
  have hstable : (prefixWord ++ tailWord_6923139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6923139).length < 2 ^ (prefixWord ++ tailWord_6923139).sum := by decide
  have hdescent : baseEnd_6923139 < baseStart_6923139 := by decide
  rcases family_descends (prefixWord ++ tailWord_6923139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6923146 : List Nat := [3, 1, 2, 4, 1, 1, 1, 1, 2, 3, 4]
def baseStart_6923146 : Nat := 118140960795 + 6923146 * 2 ^ 59
def prefixEnd_6923146 : Nat := 4983230072969 + 3 ^ 40 * 6923146 * 2
def baseEnd_6923146 : Nat := 3554901539252075393136037

theorem tailTrace_6923146 : CollatzResearch.WordTrace tailWord_6923146 prefixEnd_6923146 3554901539252075393136037 := by
  unfold tailWord_6923146
  simp only [CollatzResearch.WordTrace]
  refine ⟨63126969744157974011973323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168338585984421264031928861 63126969744157974011973323)
  ·
    refine ⟨94690454616236961017959985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63126969744157974011973323 94690454616236961017959985)
    ·
      refine ⟨71017840962177720763469989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94690454616236961017959985 71017840962177720763469989)
      ·
        refine ⟨13315845180408322643150623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71017840962177720763469989 13315845180408322643150623)
        ·
          refine ⟨19973767770612483964725935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13315845180408322643150623 19973767770612483964725935)
          ·
            refine ⟨29960651655918725947088903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19973767770612483964725935 29960651655918725947088903)
            ·
              refine ⟨44940977483878088920633355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29960651655918725947088903 44940977483878088920633355)
              ·
                refine ⟨67411466225817133380950033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44940977483878088920633355 67411466225817133380950033)
                ·
                  refine ⟨50558599669362850035712525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67411466225817133380950033 50558599669362850035712525)
                  ·
                    refine ⟨18959474876011068763392197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50558599669362850035712525 18959474876011068763392197)
                    ·
                      refine ⟨3554901539252075393136037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18959474876011068763392197 3554901539252075393136037)
                      ·
                        rfl

theorem cell23_6923146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_6923146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6923146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6923146 prefixEnd_6923146 := by exact prefixLift 6923146
  have htrace : WordTrace (prefixWord ++ tailWord_6923146) baseStart_6923146 baseEnd_6923146 := by
    simpa [prefixWord, tailWord_6923146, baseEnd_6923146] using wordTrace_append hprefix tailTrace_6923146
  have hstable : (prefixWord ++ tailWord_6923146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6923146).length < 2 ^ (prefixWord ++ tailWord_6923146).sum := by decide
  have hdescent : baseEnd_6923146 < baseStart_6923146 := by decide
  rcases family_descends (prefixWord ++ tailWord_6923146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6923156 : List Nat := [2, 4, 2, 1, 1, 1, 3, 1, 2, 6]
def baseStart_6923156 : Nat := 118140960795 + 6923156 * 2 ^ 59
def prefixEnd_6923156 : Nat := 4983230072969 + 3 ^ 40 * 6923156 * 2
def baseEnd_6923156 : Nat := 1184968891352873451336997

theorem tailTrace_6923156 : CollatzResearch.WordTrace tailWord_6923156 prefixEnd_6923156 1184968891352873451336997 := by
  unfold tailWord_6923156
  simp only [CollatzResearch.WordTrace]
  refine ⟨126254121853297833877878661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168338829137730445170504881 126254121853297833877878661)
  ·
    refine ⟨23672647847493343852102249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126254121853297833877878661 23672647847493343852102249)
    ·
      refine ⟨17754485885620007889076687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23672647847493343852102249 17754485885620007889076687)
      ·
        refine ⟨26631728828430011833615031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17754485885620007889076687 26631728828430011833615031)
        ·
          refine ⟨39947593242645017750422547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26631728828430011833615031 39947593242645017750422547)
          ·
            refine ⟨59921389863967526625633821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39947593242645017750422547 59921389863967526625633821)
            ·
              refine ⟨22470521198987822484612683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59921389863967526625633821 22470521198987822484612683)
              ·
                refine ⟨33705781798481733726919025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22470521198987822484612683 33705781798481733726919025)
                ·
                  refine ⟨25279336348861300295189269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33705781798481733726919025 25279336348861300295189269)
                  ·
                    refine ⟨1184968891352873451336997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25279336348861300295189269 1184968891352873451336997)
                    ·
                      rfl

theorem cell23_6923156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_6923156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6923156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6923156 prefixEnd_6923156 := by exact prefixLift 6923156
  have htrace : WordTrace (prefixWord ++ tailWord_6923156) baseStart_6923156 baseEnd_6923156 := by
    simpa [prefixWord, tailWord_6923156, baseEnd_6923156] using wordTrace_append hprefix tailTrace_6923156
  have hstable : (prefixWord ++ tailWord_6923156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6923156).length < 2 ^ (prefixWord ++ tailWord_6923156).sum := by decide
  have hdescent : baseEnd_6923156 < baseStart_6923156 := by decide
  rcases family_descends (prefixWord ++ tailWord_6923156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6923237 : List Nat := [1, 3, 1, 6, 1, 2, 1, 3, 5]
def baseStart_6923237 : Nat := 118140960795 + 6923237 * 2 ^ 59
def prefixEnd_6923237 : Nat := 4983230072969 + 3 ^ 40 * 6923237 * 2
def baseEnd_6923237 : Nat := 394994251776848281899791

theorem tailTrace_6923237 : CollatzResearch.WordTrace tailWord_6923237 prefixEnd_6923237 394994251776848281899791 := by
  unfold tailWord_6923237
  simp only [CollatzResearch.WordTrace]
  refine ⟨252511198019302218589455965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168340798679534812392970643 252511198019302218589455965)
  ·
    refine ⟨94691699257238331971045987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252511198019302218589455965 94691699257238331971045987)
    ·
      refine ⟨142037548885857497956568981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94691699257238331971045987 142037548885857497956568981)
      ·
        refine ⟨6658010104024570216714171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 142037548885857497956568981 6658010104024570216714171)
        ·
          refine ⟨9987015156036855325071257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6658010104024570216714171 9987015156036855325071257)
          ·
            refine ⟨7490261367027641493803443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9987015156036855325071257 7490261367027641493803443)
            ·
              refine ⟨11235392050541462240705165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7490261367027641493803443 11235392050541462240705165)
              ·
                refine ⟨4213272018953048340264437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11235392050541462240705165 4213272018953048340264437)
                ·
                  refine ⟨394994251776848281899791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4213272018953048340264437 394994251776848281899791)
                  ·
                    rfl

theorem cell23_6923237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 3, 5].length) (baseStart_6923237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6923237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6923237 prefixEnd_6923237 := by exact prefixLift 6923237
  have htrace : WordTrace (prefixWord ++ tailWord_6923237) baseStart_6923237 baseEnd_6923237 := by
    simpa [prefixWord, tailWord_6923237, baseEnd_6923237] using wordTrace_append hprefix tailTrace_6923237
  have hstable : (prefixWord ++ tailWord_6923237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6923237).length < 2 ^ (prefixWord ++ tailWord_6923237).sum := by decide
  have hdescent : baseEnd_6923237 < baseStart_6923237 := by decide
  rcases family_descends (prefixWord ++ tailWord_6923237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6923250 : List Nat := [3, 2, 1, 5, 1, 1, 1, 2, 2, 5]
def baseStart_6923250 : Nat := 118140960795 + 6923250 * 2 ^ 59
def prefixEnd_6923250 : Nat := 4983230072969 + 3 ^ 40 * 6923250 * 2
def baseEnd_6923250 : Nat := 1184984980413380995411853

theorem tailTrace_6923250 : CollatzResearch.WordTrace tailWord_6923250 prefixEnd_6923250 1184984980413380995411853 := by
  unfold tailWord_6923250
  simp only [CollatzResearch.WordTrace]
  refine ⟨63127918042063780452419801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168341114778836747873119469 63127918042063780452419801)
  ·
    refine ⟨47345938531547835339314851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63127918042063780452419801 47345938531547835339314851)
    ·
      refine ⟨71018907797321753008972277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47345938531547835339314851 71018907797321753008972277)
      ·
        refine ⟨6658022605998914344591151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71018907797321753008972277 6658022605998914344591151)
        ·
          refine ⟨9987033908998371516886727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6658022605998914344591151 9987033908998371516886727)
          ·
            refine ⟨14980550863497557275330091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9987033908998371516886727 14980550863497557275330091)
            ·
              refine ⟨22470826295246335912995137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14980550863497557275330091 22470826295246335912995137)
              ·
                refine ⟨16853119721434751934746353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22470826295246335912995137 16853119721434751934746353)
                ·
                  refine ⟨12639839791076063951059765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16853119721434751934746353 12639839791076063951059765)
                  ·
                    refine ⟨1184984980413380995411853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12639839791076063951059765 1184984980413380995411853)
                    ·
                      rfl

theorem cell23_6923250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 2, 2, 5].length) (baseStart_6923250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6923250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6923250 prefixEnd_6923250 := by exact prefixLift 6923250
  have htrace : WordTrace (prefixWord ++ tailWord_6923250) baseStart_6923250 baseEnd_6923250 := by
    simpa [prefixWord, tailWord_6923250, baseEnd_6923250] using wordTrace_append hprefix tailTrace_6923250
  have hstable : (prefixWord ++ tailWord_6923250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6923250).length < 2 ^ (prefixWord ++ tailWord_6923250).sum := by decide
  have hdescent : baseEnd_6923250 < baseStart_6923250 := by decide
  rcases family_descends (prefixWord ++ tailWord_6923250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6923357 : List Nat := [1, 4, 4, 1, 2, 1, 1, 3, 1, 5]
def baseStart_6923357 : Nat := 118140960795 + 6923357 * 2 ^ 59
def prefixEnd_6923357 : Nat := 4983230072969 + 3 ^ 40 * 6923357 * 2
def baseEnd_6923357 : Nat := 1185003294556724689199189

theorem tailTrace_6923357 : CollatzResearch.WordTrace tailWord_6923357 prefixEnd_6923357 1185003294556724689199189 := by
  unfold tailWord_6923357
  simp only [CollatzResearch.WordTrace]
  refine ⟨252515574778867479083824325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168343716519244986055882883 252515574778867479083824325)
  ·
    refine ⟨47346670271037652328217061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 252515574778867479083824325 47346670271037652328217061)
    ·
      refine ⟨8877500675819559811540699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47346670271037652328217061 8877500675819559811540699)
      ·
        refine ⟨13316251013729339717311049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8877500675819559811540699 13316251013729339717311049)
        ·
          refine ⟨9987188260297004787983287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13316251013729339717311049 9987188260297004787983287)
          ·
            refine ⟨14980782390445507181974931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9987188260297004787983287 14980782390445507181974931)
            ·
              refine ⟨22471173585668260772962397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14980782390445507181974931 22471173585668260772962397)
              ·
                refine ⟨8426690094625597789860899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22471173585668260772962397 8426690094625597789860899)
                ·
                  refine ⟨12640035141938396684791349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8426690094625597789860899 12640035141938396684791349)
                  ·
                    refine ⟨1185003294556724689199189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12640035141938396684791349 1185003294556724689199189)
                    ·
                      rfl

theorem cell23_6923357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_6923357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6923357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6923357 prefixEnd_6923357 := by exact prefixLift 6923357
  have htrace : WordTrace (prefixWord ++ tailWord_6923357) baseStart_6923357 baseEnd_6923357 := by
    simpa [prefixWord, tailWord_6923357, baseEnd_6923357] using wordTrace_append hprefix tailTrace_6923357
  have hstable : (prefixWord ++ tailWord_6923357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6923357).length < 2 ^ (prefixWord ++ tailWord_6923357).sum := by decide
  have hdescent : baseEnd_6923357 < baseStart_6923357 := by decide
  rcases family_descends (prefixWord ++ tailWord_6923357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6923360 : List Nat := [2, 1, 1, 3, 2, 2, 1, 2, 5, 2, 2]
def baseStart_6923360 : Nat := 118140960795 + 6923360 * 2 ^ 59
def prefixEnd_6923360 : Nat := 4983230072969 + 3 ^ 40 * 6923360 * 2
def baseEnd_6923360 : Nat := 3555011424112137555860053

theorem tailTrace_6923360 : CollatzResearch.WordTrace tailWord_6923360 prefixEnd_6923360 3555011424112137555860053 := by
  unfold tailWord_6923360
  simp only [CollatzResearch.WordTrace]
  refine ⟨126257842098928305298091767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168343789465237740397455689 126257842098928305298091767)
  ·
    refine ⟨189386763148392457947137651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126257842098928305298091767 189386763148392457947137651)
    ·
      refine ⟨284080144722588686920706477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189386763148392457947137651 284080144722588686920706477)
      ·
        refine ⟨106530054270970757595264929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 284080144722588686920706477 106530054270970757595264929)
        ·
          refine ⟨79897540703228068196448697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106530054270970757595264929 79897540703228068196448697)
          ·
            refine ⟨59923155527421051147336523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79897540703228068196448697 59923155527421051147336523)
            ·
              refine ⟨89884733291131576721004785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59923155527421051147336523 89884733291131576721004785)
              ·
                refine ⟨67413549968348682540753589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89884733291131576721004785 67413549968348682540753589)
                ·
                  refine ⟨6320020309532688988195649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67413549968348682540753589 6320020309532688988195649)
                  ·
                    refine ⟨4740015232149516741146737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6320020309532688988195649 4740015232149516741146737)
                    ·
                      refine ⟨3555011424112137555860053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4740015232149516741146737 3555011424112137555860053)
                      ·
                        rfl

theorem cell23_6923360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 5, 2, 2].length) (baseStart_6923360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6923360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6923360 prefixEnd_6923360 := by exact prefixLift 6923360
  have htrace : WordTrace (prefixWord ++ tailWord_6923360) baseStart_6923360 baseEnd_6923360 := by
    simpa [prefixWord, tailWord_6923360, baseEnd_6923360] using wordTrace_append hprefix tailTrace_6923360
  have hstable : (prefixWord ++ tailWord_6923360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6923360).length < 2 ^ (prefixWord ++ tailWord_6923360).sum := by decide
  have hdescent : baseEnd_6923360 < baseStart_6923360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6923360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6923370 : List Nat := [3, 1, 3, 2, 2, 2, 1, 1, 4, 4]
def baseStart_6923370 : Nat := 118140960795 + 6923370 * 2 ^ 59
def prefixEnd_6923370 : Nat := 4983230072969 + 3 ^ 40 * 6923370 * 2
def baseEnd_6923370 : Nat := 1185005519639560838911669

theorem tailTrace_6923370 : CollatzResearch.WordTrace tailWord_6923370 prefixEnd_6923370 1185005519639560838911669 := by
  unfold tailWord_6923370
  simp only [CollatzResearch.WordTrace]
  refine ⟨63129012231955095576011891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168344032618546921536031709 63129012231955095576011891)
  ·
    refine ⟨94693518347932643364017837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63129012231955095576011891 94693518347932643364017837)
    ·
      refine ⟨35510069380474741261506689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94693518347932643364017837 35510069380474741261506689)
      ·
        refine ⟨26632552035356055946130017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35510069380474741261506689 26632552035356055946130017)
        ·
          refine ⟨19974414026517041959597513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26632552035356055946130017 19974414026517041959597513)
          ·
            refine ⟨14980810519887781469698135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19974414026517041959597513 14980810519887781469698135)
            ·
              refine ⟨22471215779831672204547203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14980810519887781469698135 22471215779831672204547203)
              ·
                refine ⟨33706823669747508306820805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22471215779831672204547203 33706823669747508306820805)
                ·
                  refine ⟨6320029438077657807528901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33706823669747508306820805 6320029438077657807528901)
                  ·
                    refine ⟨1185005519639560838911669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6320029438077657807528901 1185005519639560838911669)
                    ·
                      rfl

theorem cell23_6923370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 4, 4].length) (baseStart_6923370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6923370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6923370 prefixEnd_6923370 := by exact prefixLift 6923370
  have htrace : WordTrace (prefixWord ++ tailWord_6923370) baseStart_6923370 baseEnd_6923370 := by
    simpa [prefixWord, tailWord_6923370, baseEnd_6923370] using wordTrace_append hprefix tailTrace_6923370
  have hstable : (prefixWord ++ tailWord_6923370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6923370).length < 2 ^ (prefixWord ++ tailWord_6923370).sum := by decide
  have hdescent : baseEnd_6923370 < baseStart_6923370 := by decide
  rcases family_descends (prefixWord ++ tailWord_6923370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6923397 : List Nat := [1, 3, 1, 1, 6, 1, 2, 2, 1, 2, 3]
def baseStart_6923397 : Nat := 118140960795 + 6923397 * 2 ^ 59
def prefixEnd_6923397 : Nat := 4983230072969 + 3 ^ 40 * 6923397 * 2
def baseEnd_6923397 : Nat := 3555030422896353911097383

theorem tailTrace_6923397 : CollatzResearch.WordTrace tailWord_6923397 prefixEnd_6923397 3555030422896353911097383 := by
  unfold tailWord_6923397
  simp only [CollatzResearch.WordTrace]
  refine ⟨252517033698722565915280445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168344689132481710610186963 252517033698722565915280445)
  ·
    refine ⟨94693887637020962218230167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252517033698722565915280445 94693887637020962218230167)
    ·
      refine ⟨142040831455531443327345251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94693887637020962218230167 142040831455531443327345251)
      ·
        refine ⟨213061247183297164991017877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142040831455531443327345251 213061247183297164991017877)
        ·
          refine ⟨9987245961717054608953963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 213061247183297164991017877 9987245961717054608953963)
          ·
            refine ⟨14980868942575581913430945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9987245961717054608953963 14980868942575581913430945)
            ·
              refine ⟨11235651706931686435073209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14980868942575581913430945 11235651706931686435073209)
              ·
                refine ⟨8426738780198764826304907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11235651706931686435073209 8426738780198764826304907)
                ·
                  refine ⟨12640108170298147239457361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8426738780198764826304907 12640108170298147239457361)
                  ·
                    refine ⟨9480081127723610429593021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12640108170298147239457361 9480081127723610429593021)
                    ·
                      refine ⟨3555030422896353911097383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9480081127723610429593021 3555030422896353911097383)
                      ·
                        rfl

theorem cell23_6923397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 2, 1, 2, 3].length) (baseStart_6923397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6923397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6923397 prefixEnd_6923397 := by exact prefixLift 6923397
  have htrace : WordTrace (prefixWord ++ tailWord_6923397) baseStart_6923397 baseEnd_6923397 := by
    simpa [prefixWord, tailWord_6923397, baseEnd_6923397] using wordTrace_append hprefix tailTrace_6923397
  have hstable : (prefixWord ++ tailWord_6923397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6923397).length < 2 ^ (prefixWord ++ tailWord_6923397).sum := by decide
  have hdescent : baseEnd_6923397 < baseStart_6923397 := by decide
  rcases family_descends (prefixWord ++ tailWord_6923397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6923403 : List Nat := [1, 1, 1, 1, 4, 1, 1, 2, 2, 7, 2]
def baseStart_6923403 : Nat := 118140960795 + 6923403 * 2 ^ 59
def prefixEnd_6923403 : Nat := 4983230072969 + 3 ^ 40 * 6923403 * 2
def baseEnd_6923403 : Nat := 3555033503780280887622355

theorem tailTrace_6923403 : CollatzResearch.WordTrace tailWord_6923403 prefixEnd_6923403 3555033503780280887622355 := by
  unfold tailWord_6923403
  simp only [CollatzResearch.WordTrace]
  refine ⟨252517252536700828939998863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168344835024467219293332575 252517252536700828939998863)
  ·
    refine ⟨378775878805051243409998295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252517252536700828939998863 378775878805051243409998295)
    ·
      refine ⟨568163818207576865114997443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378775878805051243409998295 568163818207576865114997443)
      ·
        refine ⟨852245727311365297672496165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 568163818207576865114997443 852245727311365297672496165)
        ·
          refine ⟨159796073870880993313593031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 852245727311365297672496165 159796073870880993313593031)
          ·
            refine ⟨239694110806321489970389547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159796073870880993313593031 239694110806321489970389547)
            ·
              refine ⟨359541166209482234955584321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239694110806321489970389547 359541166209482234955584321)
              ·
                refine ⟨269655874657111676216688241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 359541166209482234955584321 269655874657111676216688241)
                ·
                  refine ⟨202241905992833757162516181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 269655874657111676216688241 202241905992833757162516181)
                  ·
                    refine ⟨4740044671707041183496473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 202241905992833757162516181 4740044671707041183496473)
                    ·
                      refine ⟨3555033503780280887622355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4740044671707041183496473 3555033503780280887622355)
                      ·
                        rfl

theorem cell23_6923403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 7, 2].length) (baseStart_6923403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6923403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6923403 prefixEnd_6923403 := by exact prefixLift 6923403
  have htrace : WordTrace (prefixWord ++ tailWord_6923403) baseStart_6923403 baseEnd_6923403 := by
    simpa [prefixWord, tailWord_6923403, baseEnd_6923403] using wordTrace_append hprefix tailTrace_6923403
  have hstable : (prefixWord ++ tailWord_6923403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6923403).length < 2 ^ (prefixWord ++ tailWord_6923403).sum := by decide
  have hdescent : baseEnd_6923403 < baseStart_6923403 := by decide
  rcases family_descends (prefixWord ++ tailWord_6923403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6923450 : List Nat := [3, 1, 1, 1, 2, 2, 1, 5, 1, 4, 2]
def baseStart_6923450 : Nat := 118140960795 + 6923450 * 2 ^ 59
def prefixEnd_6923450 : Nat := 4983230072969 + 3 ^ 40 * 6923450 * 2
def baseEnd_6923450 : Nat := 3555057637371042203734639

theorem tailTrace_6923450 : CollatzResearch.WordTrace tailWord_6923450 prefixEnd_6923450 3555057637371042203734639 := by
  unfold tailWord_6923450
  simp only [CollatzResearch.WordTrace]
  refine ⟨63129741691882638991739951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168345977845020370644639869 63129741691882638991739951)
  ·
    refine ⟨94694612537823958487609927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63129741691882638991739951 94694612537823958487609927)
    ·
      refine ⟨142041918806735937731414891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94694612537823958487609927 142041918806735937731414891)
      ·
        refine ⟨213062878210103906597122337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142041918806735937731414891 213062878210103906597122337)
        ·
          refine ⟨159797158657577929947841753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213062878210103906597122337 159797158657577929947841753)
          ·
            refine ⟨119847868993183447460881315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159797158657577929947841753 119847868993183447460881315)
            ·
              refine ⟨179771803489775171191321973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119847868993183447460881315 179771803489775171191321973)
              ·
                refine ⟨16853606577166422299186435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 179771803489775171191321973 16853606577166422299186435)
                ·
                  refine ⟨25280409865749633448779653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16853606577166422299186435 25280409865749633448779653)
                  ·
                    refine ⟨4740076849828056271646185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25280409865749633448779653 4740076849828056271646185)
                    ·
                      refine ⟨3555057637371042203734639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4740076849828056271646185 3555057637371042203734639)
                      ·
                        rfl

theorem cell23_6923450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 5, 1, 4, 2].length) (baseStart_6923450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6923450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6923450 prefixEnd_6923450 := by exact prefixLift 6923450
  have htrace : WordTrace (prefixWord ++ tailWord_6923450) baseStart_6923450 baseEnd_6923450 := by
    simpa [prefixWord, tailWord_6923450, baseEnd_6923450] using wordTrace_append hprefix tailTrace_6923450
  have hstable : (prefixWord ++ tailWord_6923450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6923450).length < 2 ^ (prefixWord ++ tailWord_6923450).sum := by decide
  have hdescent : baseEnd_6923450 < baseStart_6923450 := by decide
  rcases family_descends (prefixWord ++ tailWord_6923450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6923453 : List Nat := [1, 4, 1, 2, 1, 1, 3, 2, 2, 1, 5]
def baseStart_6923453 : Nat := 118140960795 + 6923453 * 2 ^ 59
def prefixEnd_6923453 : Nat := 4983230072969 + 3 ^ 40 * 6923453 * 2
def baseEnd_6923453 : Nat := 3555059177813005691997125

theorem tailTrace_6923453 : CollatzResearch.WordTrace tailWord_6923453 prefixEnd_6923453 3555059177813005691997125 := by
  unfold tailWord_6923453
  simp only [CollatzResearch.WordTrace]
  refine ⟨252519076186519687479319013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168346050791013124986212675 252519076186519687479319013)
  ·
    refine ⟨47347326784972441402372315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 252519076186519687479319013 47347326784972441402372315)
    ·
      refine ⟨71020990177458662103558473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47347326784972441402372315 71020990177458662103558473)
      ·
        refine ⟨53265742633093996577668855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71020990177458662103558473 53265742633093996577668855)
        ·
          refine ⟨79898613949640994866503283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53265742633093996577668855 79898613949640994866503283)
          ·
            refine ⟨119847920924461492299754925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79898613949640994866503283 119847920924461492299754925)
            ·
              refine ⟨44942970346673059612408097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119847920924461492299754925 44942970346673059612408097)
              ·
                refine ⟨33707227760004794709306073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44942970346673059612408097 33707227760004794709306073)
                ·
                  refine ⟨25280420820003596031979555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33707227760004794709306073 25280420820003596031979555)
                  ·
                    refine ⟨37920631230005394047969333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25280420820003596031979555 37920631230005394047969333)
                    ·
                      refine ⟨3555059177813005691997125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37920631230005394047969333 3555059177813005691997125)
                      ·
                        rfl

theorem cell23_6923453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_6923453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6923453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6923453 prefixEnd_6923453 := by exact prefixLift 6923453
  have htrace : WordTrace (prefixWord ++ tailWord_6923453) baseStart_6923453 baseEnd_6923453 := by
    simpa [prefixWord, tailWord_6923453, baseEnd_6923453] using wordTrace_append hprefix tailTrace_6923453
  have hstable : (prefixWord ++ tailWord_6923453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6923453).length < 2 ^ (prefixWord ++ tailWord_6923453).sum := by decide
  have hdescent : baseEnd_6923453 < baseStart_6923453 := by decide
  rcases family_descends (prefixWord ++ tailWord_6923453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6923454 : List Nat := [4, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2]
def baseStart_6923454 : Nat := 118140960795 + 6923454 * 2 ^ 59
def prefixEnd_6923454 : Nat := 4983230072969 + 3 ^ 40 * 6923454 * 2
def baseEnd_6923454 : Nat := 3555059691293660188084621

theorem tailTrace_6923454 : CollatzResearch.WordTrace tailWord_6923454 prefixEnd_6923454 3555059691293660188084621 := by
  unfold tailWord_6923454
  simp only [CollatzResearch.WordTrace]
  refine ⟨31564889082439508081263177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168346075106344043100070277 31564889082439508081263177)
  ·
    refine ⟨23673666811829631060947383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31564889082439508081263177 23673666811829631060947383)
    ·
      refine ⟨35510500217744446591421075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23673666811829631060947383 35510500217744446591421075)
      ·
        refine ⟨53265750326616669887131613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35510500217744446591421075 53265750326616669887131613)
        ·
          refine ⟨19974656372481251207674355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53265750326616669887131613 19974656372481251207674355)
          ·
            refine ⟨29961984558721876811511533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19974656372481251207674355 29961984558721876811511533)
            ·
              refine ⟨11235744209520703804316825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29961984558721876811511533 11235744209520703804316825)
              ·
                refine ⟨8426808157140527853237619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11235744209520703804316825 8426808157140527853237619)
                ·
                  refine ⟨12640212235710791779856429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8426808157140527853237619 12640212235710791779856429)
                  ·
                    refine ⟨4740079588391546917446161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12640212235710791779856429 4740079588391546917446161)
                    ·
                      refine ⟨3555059691293660188084621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4740079588391546917446161 3555059691293660188084621)
                      ·
                        rfl

theorem cell23_6923454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2].length) (baseStart_6923454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6923454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6923454 prefixEnd_6923454 := by exact prefixLift 6923454
  have htrace : WordTrace (prefixWord ++ tailWord_6923454) baseStart_6923454 baseEnd_6923454 := by
    simpa [prefixWord, tailWord_6923454, baseEnd_6923454] using wordTrace_append hprefix tailTrace_6923454
  have hstable : (prefixWord ++ tailWord_6923454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6923454).length < 2 ^ (prefixWord ++ tailWord_6923454).sum := by decide
  have hdescent : baseEnd_6923454 < baseStart_6923454 := by decide
  rcases family_descends (prefixWord ++ tailWord_6923454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6923500 : List Nat := [2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 3]
def baseStart_6923500 : Nat := 118140960795 + 6923500 * 2 ^ 59
def prefixEnd_6923500 : Nat := 4983230072969 + 3 ^ 40 * 6923500 * 2
def baseEnd_6923500 : Nat := 3555083311403767008109409

theorem tailTrace_6923500 : CollatzResearch.WordTrace tailWord_6923500 prefixEnd_6923500 3555083311403767008109409 := by
  unfold tailWord_6923500
  simp only [CollatzResearch.WordTrace]
  refine ⟨126260395208674707253139977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168347193611566276337519969 126260395208674707253139977)
  ·
    refine ⟨94695296406506030439854983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126260395208674707253139977 94695296406506030439854983)
    ·
      refine ⟨142042944609759045659782475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94695296406506030439854983 142042944609759045659782475)
      ·
        refine ⟨213064416914638568489673713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142042944609759045659782475 213064416914638568489673713)
        ·
          refine ⟨159798312685978926367255285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213064416914638568489673713 159798312685978926367255285)
          ·
            refine ⟨14981091814310524346930183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 159798312685978926367255285 14981091814310524346930183)
            ·
              refine ⟨22471637721465786520395275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14981091814310524346930183 22471637721465786520395275)
              ·
                refine ⟨33707456582198679780592913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22471637721465786520395275 33707456582198679780592913)
                ·
                  refine ⟨25280592436649009835444685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33707456582198679780592913 25280592436649009835444685)
                  ·
                    refine ⟨9480222163743378688291757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25280592436649009835444685 9480222163743378688291757)
                    ·
                      refine ⟨3555083311403767008109409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9480222163743378688291757 3555083311403767008109409)
                      ·
                        rfl

theorem cell23_6923500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 3].length) (baseStart_6923500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6923500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6923500 prefixEnd_6923500 := by exact prefixLift 6923500
  have htrace : WordTrace (prefixWord ++ tailWord_6923500) baseStart_6923500 baseEnd_6923500 := by
    simpa [prefixWord, tailWord_6923500, baseEnd_6923500] using wordTrace_append hprefix tailTrace_6923500
  have hstable : (prefixWord ++ tailWord_6923500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6923500).length < 2 ^ (prefixWord ++ tailWord_6923500).sum := by decide
  have hdescent : baseEnd_6923500 < baseStart_6923500 := by decide
  rcases family_descends (prefixWord ++ tailWord_6923500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6923553 : List Nat := [1, 2, 3, 2, 1, 1, 1, 1, 4, 1, 6]
def baseStart_6923553 : Nat := 118140960795 + 6923553 * 2 ^ 59
def prefixEnd_6923553 : Nat := 4983230072969 + 3 ^ 40 * 6923553 * 2
def baseEnd_6923553 : Nat := 3555110525878455300746665

theorem tailTrace_6923553 : CollatzResearch.WordTrace tailWord_6923553 prefixEnd_6923553 3555110525878455300746665 := by
  unfold tailWord_6923553
  simp only [CollatzResearch.WordTrace]
  refine ⟨252522723486157404557959313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168348482324104936371972875 252522723486157404557959313)
  ·
    refine ⟨189392042614618053418469485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252522723486157404557959313 189392042614618053418469485)
    ·
      refine ⟨71022015980481770031926057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189392042614618053418469485 71022015980481770031926057)
      ·
        refine ⟨53266511985361327523944543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71022015980481770031926057 53266511985361327523944543)
        ·
          refine ⟨79899767978041991285916815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53266511985361327523944543 79899767978041991285916815)
          ·
            refine ⟨119849651967062986928875223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79899767978041991285916815 119849651967062986928875223)
            ·
              refine ⟨179774477950594480393312835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119849651967062986928875223 179774477950594480393312835)
              ·
                refine ⟨269661716925891720589969253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179774477950594480393312835 269661716925891720589969253)
                ·
                  refine ⟨50561571923604697610619235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 269661716925891720589969253 50561571923604697610619235)
                  ·
                    refine ⟨75842357885407046415928853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50561571923604697610619235 75842357885407046415928853)
                    ·
                      refine ⟨3555110525878455300746665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75842357885407046415928853 3555110525878455300746665)
                      ·
                        rfl

theorem cell23_6923553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_6923553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6923553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6923553 prefixEnd_6923553 := by exact prefixLift 6923553
  have htrace : WordTrace (prefixWord ++ tailWord_6923553) baseStart_6923553 baseEnd_6923553 := by
    simpa [prefixWord, tailWord_6923553, baseEnd_6923553] using wordTrace_append hprefix tailTrace_6923553
  have hstable : (prefixWord ++ tailWord_6923553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6923553).length < 2 ^ (prefixWord ++ tailWord_6923553).sum := by decide
  have hdescent : baseEnd_6923553 < baseStart_6923553 := by decide
  rcases family_descends (prefixWord ++ tailWord_6923553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6923557 : List Nat := [1, 3, 1, 2, 4, 1, 2, 1, 2, 4, 2]
def baseStart_6923557 : Nat := 118140960795 + 6923557 * 2 ^ 59
def prefixEnd_6923557 : Nat := 4983230072969 + 3 ^ 40 * 6923557 * 2
def baseEnd_6923557 : Nat := 3555112579801073285096647

theorem tailTrace_6923557 : CollatzResearch.WordTrace tailWord_6923557 prefixEnd_6923557 3555112579801073285096647 := by
  unfold tailWord_6923557
  simp only [CollatzResearch.WordTrace]
  refine ⟨252522869378142913241104925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168348579585428608827403283 252522869378142913241104925)
  ·
    refine ⟨94696076016803592465414347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252522869378142913241104925 94696076016803592465414347)
    ·
      refine ⟨142044114025205388698121521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94696076016803592465414347 142044114025205388698121521)
      ·
        refine ⟨106533085518904041523591141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142044114025205388698121521 106533085518904041523591141)
        ·
          refine ⟨19974953534794507785673339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106533085518904041523591141 19974953534794507785673339)
          ·
            refine ⟨29962430302191761678510009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19974953534794507785673339 29962430302191761678510009)
            ·
              refine ⟨22471822726643821258882507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29962430302191761678510009 22471822726643821258882507)
              ·
                refine ⟨33707734089965731888323761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22471822726643821258882507 33707734089965731888323761)
                ·
                  refine ⟨25280800567474298916242821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33707734089965731888323761 25280800567474298916242821)
                  ·
                    refine ⟨4740150106401431046795529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25280800567474298916242821 4740150106401431046795529)
                    ·
                      refine ⟨3555112579801073285096647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4740150106401431046795529 3555112579801073285096647)
                      ·
                        rfl

theorem cell23_6923557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 2, 4, 2].length) (baseStart_6923557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6923557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6923557 prefixEnd_6923557 := by exact prefixLift 6923557
  have htrace : WordTrace (prefixWord ++ tailWord_6923557) baseStart_6923557 baseEnd_6923557 := by
    simpa [prefixWord, tailWord_6923557, baseEnd_6923557] using wordTrace_append hprefix tailTrace_6923557
  have hstable : (prefixWord ++ tailWord_6923557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6923557).length < 2 ^ (prefixWord ++ tailWord_6923557).sum := by decide
  have hdescent : baseEnd_6923557 < baseStart_6923557 := by decide
  rcases family_descends (prefixWord ++ tailWord_6923557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6923634 : List Nat := [3, 2, 1, 2, 1, 2, 4, 1, 2, 3, 2]
def baseStart_6923634 : Nat := 118140960795 + 6923634 * 2 ^ 59
def prefixEnd_6923634 : Nat := 4983230072969 + 3 ^ 40 * 6923634 * 2
def baseEnd_6923634 : Nat := 3555152117811469483833793

theorem tailTrace_6923634 : CollatzResearch.WordTrace tailWord_6923634 prefixEnd_6923634 3555152117811469483833793 := by
  unfold tailWord_6923634
  simp only [CollatzResearch.WordTrace]
  refine ⟨63131419449715988847914489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168350451865909303594438637 63131419449715988847914489)
  ·
    refine ⟨47348564587286991635935867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63131419449715988847914489 47348564587286991635935867)
    ·
      refine ⟨71022846880930487453903801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47348564587286991635935867 71022846880930487453903801)
      ·
        refine ⟨53267135160697865590427851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71022846880930487453903801 53267135160697865590427851)
        ·
          refine ⟨79900702741046798385641777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53267135160697865590427851 79900702741046798385641777)
          ·
            refine ⟨59925527055785098789231333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79900702741046798385641777 59925527055785098789231333)
            ·
              refine ⟨11236036322959706022980875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59925527055785098789231333 11236036322959706022980875)
              ·
                refine ⟨16854054484439559034471313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11236036322959706022980875 16854054484439559034471313)
                ·
                  refine ⟨12640540863329669275853485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16854054484439559034471313 12640540863329669275853485)
                  ·
                    refine ⟨4740202823748625978445057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12640540863329669275853485 4740202823748625978445057)
                    ·
                      refine ⟨3555152117811469483833793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4740202823748625978445057 3555152117811469483833793)
                      ·
                        rfl

theorem cell23_6923634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 1, 2, 3, 2].length) (baseStart_6923634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6923634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6923634 prefixEnd_6923634 := by exact prefixLift 6923634
  have htrace : WordTrace (prefixWord ++ tailWord_6923634) baseStart_6923634 baseEnd_6923634 := by
    simpa [prefixWord, tailWord_6923634, baseEnd_6923634] using wordTrace_append hprefix tailTrace_6923634
  have hstable : (prefixWord ++ tailWord_6923634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6923634).length < 2 ^ (prefixWord ++ tailWord_6923634).sum := by decide
  have hdescent : baseEnd_6923634 < baseStart_6923634 := by decide
  rcases family_descends (prefixWord ++ tailWord_6923634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6923660 : List Nat := [2, 2, 1, 2, 1, 3, 1, 2, 3, 2, 4]
def baseStart_6923660 : Nat := 118140960795 + 6923660 * 2 ^ 59
def prefixEnd_6923660 : Nat := 4983230072969 + 3 ^ 40 * 6923660 * 2
def baseEnd_6923660 : Nat := 3555165468308486382108673

theorem tailTrace_6923660 : CollatzResearch.WordTrace tailWord_6923660 prefixEnd_6923660 3555165468308486382108673 := by
  unfold tailWord_6923660
  simp only [CollatzResearch.WordTrace]
  refine ⟨126263313048384880916052217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168351084064513174554736289 126263313048384880916052217)
  ·
    refine ⟨94697484786288660687039163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126263313048384880916052217 94697484786288660687039163)
    ·
      refine ⟨142046227179432991030558745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94697484786288660687039163 142046227179432991030558745)
      ·
        refine ⟨106534670384574743272919059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142046227179432991030558745 106534670384574743272919059)
        ·
          refine ⟨159802005576862114909378589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106534670384574743272919059 159802005576862114909378589)
          ·
            refine ⟨59925752091323293091016971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159802005576862114909378589 59925752091323293091016971)
            ·
              refine ⟨89888628136984939636525457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59925752091323293091016971 89888628136984939636525457)
              ·
                refine ⟨67416471102738704727394093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89888628136984939636525457 67416471102738704727394093)
                ·
                  refine ⟨25281176663527014272772785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67416471102738704727394093 25281176663527014272772785)
                  ·
                    refine ⟨18960882497645260704579589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25281176663527014272772785 18960882497645260704579589)
                    ·
                      refine ⟨3555165468308486382108673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18960882497645260704579589 3555165468308486382108673)
                      ·
                        rfl

theorem cell23_6923660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 3, 2, 4].length) (baseStart_6923660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6923660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6923660 prefixEnd_6923660 := by exact prefixLift 6923660
  have htrace : WordTrace (prefixWord ++ tailWord_6923660) baseStart_6923660 baseEnd_6923660 := by
    simpa [prefixWord, tailWord_6923660, baseEnd_6923660] using wordTrace_append hprefix tailTrace_6923660
  have hstable : (prefixWord ++ tailWord_6923660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6923660).length < 2 ^ (prefixWord ++ tailWord_6923660).sum := by decide
  have hdescent : baseEnd_6923660 < baseStart_6923660 := by decide
  rcases family_descends (prefixWord ++ tailWord_6923660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6923677 : List Nat := [1, 4, 2, 1, 3, 1, 1, 3, 1, 2, 4]
def baseStart_6923677 : Nat := 118140960795 + 6923677 * 2 ^ 59
def prefixEnd_6923677 : Nat := 4983230072969 + 3 ^ 40 * 6923677 * 2
def baseEnd_6923677 : Nat := 3555174197479612815596095

theorem tailTrace_6923677 : CollatzResearch.WordTrace tailWord_6923677 prefixEnd_6923677 3555174197479612815596095 := by
  unfold tailWord_6923677
  simp only [CollatzResearch.WordTrace]
  refine ⟨252527246137708173735473285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168351497425138782490315523 252527246137708173735473285)
  ·
    refine ⟨47348858650820282575401241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 252527246137708173735473285 47348858650820282575401241)
    ·
      refine ⟨35511643988115211931550931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47348858650820282575401241 35511643988115211931550931)
      ·
        refine ⟨53267465982172817897326397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35511643988115211931550931 53267465982172817897326397)
        ·
          refine ⟨19975299743314806711497399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53267465982172817897326397 19975299743314806711497399)
          ·
            refine ⟨29962949614972210067246099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19975299743314806711497399 29962949614972210067246099)
            ·
              refine ⟨44944424422458315100869149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29962949614972210067246099 44944424422458315100869149)
              ·
                refine ⟨16854159158421868162825931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44944424422458315100869149 16854159158421868162825931)
                ·
                  refine ⟨25281238737632802244238897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16854159158421868162825931 25281238737632802244238897)
                  ·
                    refine ⟨18960929053224601683179173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25281238737632802244238897 18960929053224601683179173)
                    ·
                      refine ⟨3555174197479612815596095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18960929053224601683179173 3555174197479612815596095)
                      ·
                        rfl

theorem cell23_6923677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_6923677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6923677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6923677 prefixEnd_6923677 := by exact prefixLift 6923677
  have htrace : WordTrace (prefixWord ++ tailWord_6923677) baseStart_6923677 baseEnd_6923677 := by
    simpa [prefixWord, tailWord_6923677, baseEnd_6923677] using wordTrace_append hprefix tailTrace_6923677
  have hstable : (prefixWord ++ tailWord_6923677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6923677).length < 2 ^ (prefixWord ++ tailWord_6923677).sum := by decide
  have hdescent : baseEnd_6923677 < baseStart_6923677 := by decide
  rcases family_descends (prefixWord ++ tailWord_6923677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6923687 : List Nat := [1, 1, 6, 1, 1, 1, 5, 7]
def baseStart_6923687 : Nat := 118140960795 + 6923687 * 2 ^ 59
def prefixEnd_6923687 : Nat := 4983230072969 + 3 ^ 40 * 6923687 * 2
def baseEnd_6923687 : Nat := 131673308603191028758187

theorem tailTrace_6923687 : CollatzResearch.WordTrace tailWord_6923687 prefixEnd_6923687 131673308603191028758187 := by
  unfold tailWord_6923687
  simp only [CollatzResearch.WordTrace]
  refine ⟨252527610867671945443337315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168351740578447963628891543 252527610867671945443337315)
  ·
    refine ⟨378791416301507918165005973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252527610867671945443337315 378791416301507918165005973)
    ·
      refine ⟨17755847639133183663984655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 378791416301507918165005973 17755847639133183663984655)
      ·
        refine ⟨26633771458699775495976983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17755847639133183663984655 26633771458699775495976983)
        ·
          refine ⟨39950657188049663243965475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26633771458699775495976983 39950657188049663243965475)
          ·
            refine ⟨59925985782074494865948213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39950657188049663243965475 59925985782074494865948213)
            ·
              refine ⟨5618061167069483893682645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59925985782074494865948213 5618061167069483893682645)
              ·
                refine ⟨131673308603191028758187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5618061167069483893682645 131673308603191028758187)
                ·
                  rfl

theorem cell23_6923687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 5, 7].length) (baseStart_6923687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6923687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6923687 prefixEnd_6923687 := by exact prefixLift 6923687
  have htrace : WordTrace (prefixWord ++ tailWord_6923687) baseStart_6923687 baseEnd_6923687 := by
    simpa [prefixWord, tailWord_6923687, baseEnd_6923687] using wordTrace_append hprefix tailTrace_6923687
  have hstable : (prefixWord ++ tailWord_6923687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6923687).length < 2 ^ (prefixWord ++ tailWord_6923687).sum := by decide
  have hdescent : baseEnd_6923687 < baseStart_6923687 := by decide
  rcases family_descends (prefixWord ++ tailWord_6923687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6923697 : List Nat := [1, 2, 2, 4, 1, 1, 1, 4, 1, 3, 3]
def baseStart_6923697 : Nat := 118140960795 + 6923697 * 2 ^ 59
def prefixEnd_6923697 : Nat := 4983230072969 + 3 ^ 40 * 6923697 * 2
def baseEnd_6923697 : Nat := 3555184467092702737346003

theorem tailTrace_6923697 : CollatzResearch.WordTrace tailWord_6923697 prefixEnd_6923697 3555184467092702737346003 := by
  unfold tailWord_6923697
  simp only [CollatzResearch.WordTrace]
  refine ⟨252527975597635717151201345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168351983731757144767467563 252527975597635717151201345)
  ·
    refine ⟨189395981698226787863401009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252527975597635717151201345 189395981698226787863401009)
    ·
      refine ⟨142046986273670090897550757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189395981698226787863401009 142046986273670090897550757)
      ·
        refine ⟨26633809926313142043290767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142046986273670090897550757 26633809926313142043290767)
        ·
          refine ⟨39950714889469713064936151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26633809926313142043290767 39950714889469713064936151)
          ·
            refine ⟨59926072334204569597404227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39950714889469713064936151 59926072334204569597404227)
            ·
              refine ⟨89889108501306854396106341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59926072334204569597404227 89889108501306854396106341)
              ·
                refine ⟨16854207843995035199269939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89889108501306854396106341 16854207843995035199269939)
                ·
                  refine ⟨25281311765992552798904909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16854207843995035199269939 25281311765992552798904909)
                  ·
                    refine ⟨9480491912247207299589341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25281311765992552798904909 9480491912247207299589341)
                    ·
                      refine ⟨3555184467092702737346003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9480491912247207299589341 3555184467092702737346003)
                      ·
                        rfl

theorem cell23_6923697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_6923697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6923697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6923697 prefixEnd_6923697 := by exact prefixLift 6923697
  have htrace : WordTrace (prefixWord ++ tailWord_6923697) baseStart_6923697 baseEnd_6923697 := by
    simpa [prefixWord, tailWord_6923697, baseEnd_6923697] using wordTrace_append hprefix tailTrace_6923697
  have hstable : (prefixWord ++ tailWord_6923697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6923697).length < 2 ^ (prefixWord ++ tailWord_6923697).sum := by decide
  have hdescent : baseEnd_6923697 < baseStart_6923697 := by decide
  rcases family_descends (prefixWord ++ tailWord_6923697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6923701 : List Nat := [1, 3, 3, 2, 2, 1, 4, 1, 1, 2, 3]
def baseStart_6923701 : Nat := 118140960795 + 6923701 * 2 ^ 59
def prefixEnd_6923701 : Nat := 4983230072969 + 3 ^ 40 * 6923701 * 2
def baseEnd_6923701 : Nat := 3555186521015320721695985

theorem tailTrace_6923701 : CollatzResearch.WordTrace tailWord_6923701 prefixEnd_6923701 3555186521015320721695985 := by
  unfold tailWord_6923701
  simp only [CollatzResearch.WordTrace]
  refine ⟨252528121489621225834346957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168352080993080817222897971 252528121489621225834346957)
  ·
    refine ⟨94698045558607959687880109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252528121489621225834346957 94698045558607959687880109)
    ·
      refine ⟨35511767084477984882955041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94698045558607959687880109 35511767084477984882955041)
      ·
        refine ⟨26633825313358488662216281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35511767084477984882955041 26633825313358488662216281)
        ·
          refine ⟨19975368985018866496662211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26633825313358488662216281 19975368985018866496662211)
          ·
            refine ⟨29963053477528299744993317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19975368985018866496662211 29963053477528299744993317)
            ·
              refine ⟨5618072527036556202186247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29963053477528299744993317 5618072527036556202186247)
              ·
                refine ⟨8427108790554834303279371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5618072527036556202186247 8427108790554834303279371)
                ·
                  refine ⟨12640663185832251454919057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8427108790554834303279371 12640663185832251454919057)
                  ·
                    refine ⟨9480497389374188591189293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12640663185832251454919057 9480497389374188591189293)
                    ·
                      refine ⟨3555186521015320721695985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9480497389374188591189293 3555186521015320721695985)
                      ·
                        rfl

theorem cell23_6923701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 4, 1, 1, 2, 3].length) (baseStart_6923701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6923701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6923701 prefixEnd_6923701 := by exact prefixLift 6923701
  have htrace : WordTrace (prefixWord ++ tailWord_6923701) baseStart_6923701 baseEnd_6923701 := by
    simpa [prefixWord, tailWord_6923701, baseEnd_6923701] using wordTrace_append hprefix tailTrace_6923701
  have hstable : (prefixWord ++ tailWord_6923701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6923701).length < 2 ^ (prefixWord ++ tailWord_6923701).sum := by decide
  have hdescent : baseEnd_6923701 < baseStart_6923701 := by decide
  rcases family_descends (prefixWord ++ tailWord_6923701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6923708 : List Nat := [2, 2, 2, 4, 3, 1, 1, 2, 2, 4]
def baseStart_6923708 : Nat := 118140960795 + 6923708 * 2 ^ 59
def prefixEnd_6923708 : Nat := 4983230072969 + 3 ^ 40 * 6923708 * 2
def baseEnd_6923708 : Nat := 1185063371793300731436151

theorem tailTrace_6923708 : CollatzResearch.WordTrace tailWord_6923708 prefixEnd_6923708 1185063371793300731436151 := by
  unfold tailWord_6923708
  simp only [CollatzResearch.WordTrace]
  refine ⟨126264188400297933014925889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168352251200397244019901185 126264188400297933014925889)
  ·
    refine ⟨94698141300223449761194417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126264188400297933014925889 94698141300223449761194417)
    ·
      refine ⟨71023605975167587320895813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94698141300223449761194417 71023605975167587320895813)
      ·
        refine ⟨13316926120343922622667965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71023605975167587320895813 13316926120343922622667965)
        ·
          refine ⟨4993847295128970983500487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13316926120343922622667965 4993847295128970983500487)
          ·
            refine ⟨7490770942693456475250731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4993847295128970983500487 7490770942693456475250731)
            ·
              refine ⟨11236156414040184712876097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7490770942693456475250731 11236156414040184712876097)
              ·
                refine ⟨8427117310530138534657073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11236156414040184712876097 8427117310530138534657073)
                ·
                  refine ⟨6320337982897603900992805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8427117310530138534657073 6320337982897603900992805)
                  ·
                    refine ⟨1185063371793300731436151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6320337982897603900992805 1185063371793300731436151)
                    ·
                      rfl

theorem cell23_6923708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 2, 2, 4].length) (baseStart_6923708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6923708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6923708 prefixEnd_6923708 := by exact prefixLift 6923708
  have htrace : WordTrace (prefixWord ++ tailWord_6923708) baseStart_6923708 baseEnd_6923708 := by
    simpa [prefixWord, tailWord_6923708, baseEnd_6923708] using wordTrace_append hprefix tailTrace_6923708
  have hstable : (prefixWord ++ tailWord_6923708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6923708).length < 2 ^ (prefixWord ++ tailWord_6923708).sum := by decide
  have hdescent : baseEnd_6923708 < baseStart_6923708 := by decide
  rcases family_descends (prefixWord ++ tailWord_6923708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6923741 : List Nat := [1, 4, 3, 1, 1, 2, 1, 4, 1, 3, 2]
def baseStart_6923741 : Nat := 118140960795 + 6923741 * 2 ^ 59
def prefixEnd_6923741 : Nat := 4983230072969 + 3 ^ 40 * 6923741 * 2
def baseEnd_6923741 : Nat := 3555207060241500565195801

theorem tailTrace_6923741 : CollatzResearch.WordTrace tailWord_6923741 prefixEnd_6923741 3555207060241500565195801 := by
  unfold tailWord_6923741
  simp only [CollatzResearch.WordTrace]
  refine ⟨252529580409476312665803077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168353053606317541777202051 252529580409476312665803077)
  ·
    refine ⟨47349296326776808624838077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 252529580409476312665803077 47349296326776808624838077)
    ·
      refine ⟨17755986122541303234314279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47349296326776808624838077 17755986122541303234314279)
      ·
        refine ⟨26633979183811954851471419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17755986122541303234314279 26633979183811954851471419)
        ·
          refine ⟨39950968775717932277207129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26633979183811954851471419 39950968775717932277207129)
          ·
            refine ⟨29963226581788449207905347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39950968775717932277207129 29963226581788449207905347)
            ·
              refine ⟨44944839872682673811858021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29963226581788449207905347 44944839872682673811858021)
              ·
                refine ⟨8427157476128001339723379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44944839872682673811858021 8427157476128001339723379)
                ·
                  refine ⟨12640736214192002009585069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8427157476128001339723379 12640736214192002009585069)
                  ·
                    refine ⟨4740276080322000753594401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12640736214192002009585069 4740276080322000753594401)
                    ·
                      refine ⟨3555207060241500565195801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4740276080322000753594401 3555207060241500565195801)
                      ·
                        rfl

theorem cell23_6923741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 4, 1, 3, 2].length) (baseStart_6923741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6923741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6923741 prefixEnd_6923741 := by exact prefixLift 6923741
  have htrace : WordTrace (prefixWord ++ tailWord_6923741) baseStart_6923741 baseEnd_6923741 := by
    simpa [prefixWord, tailWord_6923741, baseEnd_6923741] using wordTrace_append hprefix tailTrace_6923741
  have hstable : (prefixWord ++ tailWord_6923741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6923741).length < 2 ^ (prefixWord ++ tailWord_6923741).sum := by decide
  have hdescent : baseEnd_6923741 < baseStart_6923741 := by decide
  rcases family_descends (prefixWord ++ tailWord_6923741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6923770 : List Nat := [3, 1, 1, 1, 1, 2, 3, 1, 1, 2, 7]
def baseStart_6923770 : Nat := 118140960795 + 6923770 * 2 ^ 59
def prefixEnd_6923770 : Nat := 4983230072969 + 3 ^ 40 * 6923770 * 2
def baseEnd_6923770 : Nat := 3555221951180480951733167

theorem tailTrace_6923770 : CollatzResearch.WordTrace tailWord_6923770 prefixEnd_6923770 3555221951180480951733167 := by
  unfold tailWord_6923770
  simp only [CollatzResearch.WordTrace]
  refine ⟨63132659531592812654652191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168353758750914167079072509 63132659531592812654652191)
  ·
    refine ⟨94698989297389218981978287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63132659531592812654652191 94698989297389218981978287)
    ·
      refine ⟨142048483946083828472967431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94698989297389218981978287 142048483946083828472967431)
      ·
        refine ⟨213072725919125742709451147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142048483946083828472967431 213072725919125742709451147)
        ·
          refine ⟨319609088878688614064176721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213072725919125742709451147 319609088878688614064176721)
          ·
            refine ⟨239706816659016460548132541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 319609088878688614064176721 239706816659016460548132541)
            ·
              refine ⟨89890056247131172705549703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 239706816659016460548132541 89890056247131172705549703)
              ·
                refine ⟨134835084370696759058324555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89890056247131172705549703 134835084370696759058324555)
                ·
                  refine ⟨202252626556045138587486833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134835084370696759058324555 202252626556045138587486833)
                  ·
                    refine ⟨151689469917033853940615125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 202252626556045138587486833 151689469917033853940615125)
                    ·
                      refine ⟨3555221951180480951733167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 151689469917033853940615125 3555221951180480951733167)
                      ·
                        rfl

theorem cell23_6923770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 1, 2, 7].length) (baseStart_6923770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6923770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6923770 prefixEnd_6923770 := by exact prefixLift 6923770
  have htrace : WordTrace (prefixWord ++ tailWord_6923770) baseStart_6923770 baseEnd_6923770 := by
    simpa [prefixWord, tailWord_6923770, baseEnd_6923770] using wordTrace_append hprefix tailTrace_6923770
  have hstable : (prefixWord ++ tailWord_6923770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6923770).length < 2 ^ (prefixWord ++ tailWord_6923770).sum := by decide
  have hdescent : baseEnd_6923770 < baseStart_6923770 := by decide
  rcases family_descends (prefixWord ++ tailWord_6923770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6923782 : List Nat := [6, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3]
def baseStart_6923782 : Nat := 118140960795 + 6923782 * 2 ^ 59
def prefixEnd_6923782 : Nat := 4983230072969 + 3 ^ 40 * 6923782 * 2
def baseEnd_6923782 : Nat := 3555228112948334904783113

theorem tailTrace_6923782 : CollatzResearch.WordTrace tailWord_6923782 prefixEnd_6923782 3555228112948334904783113 := by
  unfold tailWord_6923782
  simp only [CollatzResearch.WordTrace]
  refine ⟨7891596118822743020876425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 168354050534885184445363733 7891596118822743020876425)
  ·
    refine ⟨5918697089117057265657319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7891596118822743020876425 5918697089117057265657319)
    ·
      refine ⟨8878045633675585898485979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5918697089117057265657319 8878045633675585898485979)
      ·
        refine ⟨13317068450513378847728969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8878045633675585898485979 13317068450513378847728969)
        ·
          refine ⟨9987801337885034135796727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13317068450513378847728969 9987801337885034135796727)
          ·
            refine ⟨14981702006827551203695091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9987801337885034135796727 14981702006827551203695091)
            ·
              refine ⟨22472553010241326805542637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14981702006827551203695091 22472553010241326805542637)
              ·
                refine ⟨8427207378840497552078489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22472553010241326805542637 8427207378840497552078489)
                ·
                  refine ⟨6320405534130373164058867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8427207378840497552078489 6320405534130373164058867)
                  ·
                    refine ⟨9480608301195559746088301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6320405534130373164058867 9480608301195559746088301)
                    ·
                      refine ⟨3555228112948334904783113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9480608301195559746088301 3555228112948334904783113)
                      ·
                        rfl

theorem cell23_6923782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_6923782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6923782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6923782 prefixEnd_6923782 := by exact prefixLift 6923782
  have htrace : WordTrace (prefixWord ++ tailWord_6923782) baseStart_6923782 baseEnd_6923782 := by
    simpa [prefixWord, tailWord_6923782, baseEnd_6923782] using wordTrace_append hprefix tailTrace_6923782
  have hstable : (prefixWord ++ tailWord_6923782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6923782).length < 2 ^ (prefixWord ++ tailWord_6923782).sum := by decide
  have hdescent : baseEnd_6923782 < baseStart_6923782 := by decide
  rcases family_descends (prefixWord ++ tailWord_6923782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6923788 : List Nat := [2, 2, 1, 2, 5, 1, 1, 3, 2, 2, 2]
def baseStart_6923788 : Nat := 118140960795 + 6923788 * 2 ^ 59
def prefixEnd_6923788 : Nat := 4983230072969 + 3 ^ 40 * 6923788 * 2
def baseEnd_6923788 : Nat := 3555231193832261881308085

theorem tailTrace_6923788 : CollatzResearch.WordTrace tailWord_6923788 prefixEnd_6923788 3555231193832261881308085 := by
  unfold tailWord_6923788
  simp only [CollatzResearch.WordTrace]
  refine ⟨126265647320153019846382009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168354196426870693128509345 126265647320153019846382009)
  ·
    refine ⟨94699235490114764884786507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126265647320153019846382009 94699235490114764884786507)
    ·
      refine ⟨142048853235172147327179761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94699235490114764884786507 142048853235172147327179761)
      ·
        refine ⟨106536639926379110495384821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142048853235172147327179761 106536639926379110495384821)
        ·
          refine ⟨9987809993098041608942327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 106536639926379110495384821 9987809993098041608942327)
          ·
            refine ⟨14981714989647062413413491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9987809993098041608942327 14981714989647062413413491)
            ·
              refine ⟨22472572484470593620120237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14981714989647062413413491 22472572484470593620120237)
              ·
                refine ⟨8427214681676472607545089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22472572484470593620120237 8427214681676472607545089)
                ·
                  refine ⟨6320411011257354455658817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8427214681676472607545089 6320411011257354455658817)
                  ·
                    refine ⟨4740308258443015841744113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6320411011257354455658817 4740308258443015841744113)
                    ·
                      refine ⟨3555231193832261881308085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4740308258443015841744113 3555231193832261881308085)
                      ·
                        rfl

theorem cell23_6923788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 3, 2, 2, 2].length) (baseStart_6923788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6923788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6923788 prefixEnd_6923788 := by exact prefixLift 6923788
  have htrace : WordTrace (prefixWord ++ tailWord_6923788) baseStart_6923788 baseEnd_6923788 := by
    simpa [prefixWord, tailWord_6923788, baseEnd_6923788] using wordTrace_append hprefix tailTrace_6923788
  have hstable : (prefixWord ++ tailWord_6923788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6923788).length < 2 ^ (prefixWord ++ tailWord_6923788).sum := by decide
  have hdescent : baseEnd_6923788 < baseStart_6923788 := by decide
  rcases family_descends (prefixWord ++ tailWord_6923788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6923807 : List Nat := [1, 1, 2, 4, 1, 1, 3, 3, 2, 5]
def baseStart_6923807 : Nat := 118140960795 + 6923807 * 2 ^ 59
def prefixEnd_6923807 : Nat := 4983230072969 + 3 ^ 40 * 6923807 * 2
def baseEnd_6923807 : Nat := 1185080316654899102323499

theorem tailTrace_6923807 : CollatzResearch.WordTrace tailWord_6923807 prefixEnd_6923807 1185080316654899102323499 := by
  unfold tailWord_6923807
  simp only [CollatzResearch.WordTrace]
  refine ⟨252531987627237205937705675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168354658418158137291803783 252531987627237205937705675)
  ·
    refine ⟨378797981440855808906558513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252531987627237205937705675 378797981440855808906558513)
    ·
      refine ⟨284098486080641856679918885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 378797981440855808906558513 284098486080641856679918885)
      ·
        refine ⟨53268466140120348127484791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 284098486080641856679918885 53268466140120348127484791)
        ·
          refine ⟨79902699210180522191227187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53268466140120348127484791 79902699210180522191227187)
          ·
            refine ⟨119854048815270783286840781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79902699210180522191227187 119854048815270783286840781)
            ·
              refine ⟨44945268305726543732565293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119854048815270783286840781 44945268305726543732565293)
              ·
                refine ⟨16854475614647453899711985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44945268305726543732565293 16854475614647453899711985)
                ·
                  refine ⟨12640856710985590424783989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16854475614647453899711985 12640856710985590424783989)
                  ·
                    refine ⟨1185080316654899102323499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12640856710985590424783989 1185080316654899102323499)
                    ·
                      rfl

theorem cell23_6923807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 3, 2, 5].length) (baseStart_6923807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6923807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6923807 prefixEnd_6923807 := by exact prefixLift 6923807
  have htrace : WordTrace (prefixWord ++ tailWord_6923807) baseStart_6923807 baseEnd_6923807 := by
    simpa [prefixWord, tailWord_6923807, baseEnd_6923807] using wordTrace_append hprefix tailTrace_6923807
  have hstable : (prefixWord ++ tailWord_6923807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6923807).length < 2 ^ (prefixWord ++ tailWord_6923807).sum := by decide
  have hdescent : baseEnd_6923807 < baseStart_6923807 := by decide
  rcases family_descends (prefixWord ++ tailWord_6923807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6923901 : List Nat := [1, 4, 1, 1, 4, 2, 3, 1, 6]
def baseStart_6923901 : Nat := 118140960795 + 6923901 * 2 ^ 59
def prefixEnd_6923901 : Nat := 4983230072969 + 3 ^ 40 * 6923901 * 2
def baseEnd_6923901 : Nat := 395032135238468882132785

theorem tailTrace_6923901 : CollatzResearch.WordTrace tailWord_6923901 prefixEnd_6923901 395032135238468882132785 := by
  unfold tailWord_6923901
  simp only [CollatzResearch.WordTrace]
  refine ⟨252535416088896659991627557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168356944059264439994418371 252535416088896659991627557)
  ·
    refine ⟨47350390516668123748430167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 252535416088896659991627557 47350390516668123748430167)
    ·
      refine ⟨71025585775002185622645251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47350390516668123748430167 71025585775002185622645251)
      ·
        refine ⟨106538378662503278433967877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71025585775002185622645251 106538378662503278433967877)
        ·
          refine ⟨19975945999219364706368977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106538378662503278433967877 19975945999219364706368977)
          ·
            refine ⟨14981959499414523529776733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19975945999219364706368977 14981959499414523529776733)
            ·
              refine ⟨5618234812280446323666275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14981959499414523529776733 5618234812280446323666275)
              ·
                refine ⟨8427352218420669485499413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5618234812280446323666275 8427352218420669485499413)
                ·
                  refine ⟨395032135238468882132785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8427352218420669485499413 395032135238468882132785)
                  ·
                    rfl

theorem cell23_6923901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 3, 1, 6].length) (baseStart_6923901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6923901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6923901 prefixEnd_6923901 := by exact prefixLift 6923901
  have htrace : WordTrace (prefixWord ++ tailWord_6923901) baseStart_6923901 baseEnd_6923901 := by
    simpa [prefixWord, tailWord_6923901, baseEnd_6923901] using wordTrace_append hprefix tailTrace_6923901
  have hstable : (prefixWord ++ tailWord_6923901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6923901).length < 2 ^ (prefixWord ++ tailWord_6923901).sum := by decide
  have hdescent : baseEnd_6923901 < baseStart_6923901 := by decide
  rcases family_descends (prefixWord ++ tailWord_6923901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6923904 : List Nat := [2, 1, 1, 2, 1, 4, 1, 1, 3, 5, 2]
def baseStart_6923904 : Nat := 118140960795 + 6923904 * 2 ^ 59
def prefixEnd_6923904 : Nat := 4983230072969 + 3 ^ 40 * 6923904 * 2
def baseEnd_6923904 : Nat := 3555290757588183427457551

theorem tailTrace_6923904 : CollatzResearch.WordTrace tailWord_6923904 prefixEnd_6923904 3555290757588183427457551 := by
  unfold tailWord_6923904
  simp only [CollatzResearch.WordTrace]
  refine ⟨126267762753942895751993383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168357017005257194335991177 126267762753942895751993383)
  ·
    refine ⟨189401644130914343627990075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126267762753942895751993383 189401644130914343627990075)
    ·
      refine ⟨284102466196371515441985113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189401644130914343627990075 284102466196371515441985113)
      ·
        refine ⟨213076849647278636581488835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 284102466196371515441985113 213076849647278636581488835)
        ·
          refine ⟨319615274470917954872233253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213076849647278636581488835 319615274470917954872233253)
          ·
            refine ⟨59927863963297116538543735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 319615274470917954872233253 59927863963297116538543735)
            ·
              refine ⟨89891795944945674807815603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59927863963297116538543735 89891795944945674807815603)
              ·
                refine ⟨134837693917418512211723405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89891795944945674807815603 134837693917418512211723405)
                ·
                  refine ⟨50564135219031942079396277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 134837693917418512211723405 50564135219031942079396277)
                  ·
                    refine ⟨4740387676784244569943401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50564135219031942079396277 4740387676784244569943401)
                    ·
                      refine ⟨3555290757588183427457551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4740387676784244569943401 3555290757588183427457551)
                      ·
                        rfl

theorem cell23_6923904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 3, 5, 2].length) (baseStart_6923904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6923904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6923904 prefixEnd_6923904 := by exact prefixLift 6923904
  have htrace : WordTrace (prefixWord ++ tailWord_6923904) baseStart_6923904 baseEnd_6923904 := by
    simpa [prefixWord, tailWord_6923904, baseEnd_6923904] using wordTrace_append hprefix tailTrace_6923904
  have hstable : (prefixWord ++ tailWord_6923904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6923904).length < 2 ^ (prefixWord ++ tailWord_6923904).sum := by decide
  have hdescent : baseEnd_6923904 < baseStart_6923904 := by decide
  rcases family_descends (prefixWord ++ tailWord_6923904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6923911 : List Nat := [1, 1, 4, 2, 1, 3, 2, 2, 3, 1, 3]
def baseStart_6923911 : Nat := 118140960795 + 6923911 * 2 ^ 59
def prefixEnd_6923911 : Nat := 4983230072969 + 3 ^ 40 * 6923911 * 2
def baseEnd_6923911 : Nat := 3555294351952764900070019

theorem tailTrace_6923911 : CollatzResearch.WordTrace tailWord_6923911 prefixEnd_6923911 3555294351952764900070019 := by
  unfold tailWord_6923911
  simp only [CollatzResearch.WordTrace]
  refine ⟨252535780818860431699491587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168357187212573621132994391 252535780818860431699491587)
  ·
    refine ⟨378803671228290647549237381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252535780818860431699491587 378803671228290647549237381)
    ·
      refine ⟨71025688355304496415482009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 378803671228290647549237381 71025688355304496415482009)
      ·
        refine ⟨53269266266478372311611507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71025688355304496415482009 53269266266478372311611507)
        ·
          refine ⟨79903899399717558467417261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53269266266478372311611507 79903899399717558467417261)
          ·
            refine ⟨29963962274894084425281473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79903899399717558467417261 29963962274894084425281473)
            ·
              refine ⟨22472971706170563318961105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29963962274894084425281473 22472971706170563318961105)
              ·
                refine ⟨16854728779627922489220829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22472971706170563318961105 16854728779627922489220829)
                ·
                  refine ⟨6320523292360470933457811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16854728779627922489220829 6320523292360470933457811)
                  ·
                    refine ⟨9480784938540706400186717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6320523292360470933457811 9480784938540706400186717)
                    ·
                      refine ⟨3555294351952764900070019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9480784938540706400186717 3555294351952764900070019)
                      ·
                        rfl

theorem cell23_6923911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 2, 3, 1, 3].length) (baseStart_6923911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6923911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6923911 prefixEnd_6923911 := by exact prefixLift 6923911
  have htrace : WordTrace (prefixWord ++ tailWord_6923911) baseStart_6923911 baseEnd_6923911 := by
    simpa [prefixWord, tailWord_6923911, baseEnd_6923911] using wordTrace_append hprefix tailTrace_6923911
  have hstable : (prefixWord ++ tailWord_6923911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6923911).length < 2 ^ (prefixWord ++ tailWord_6923911).sum := by decide
  have hdescent : baseEnd_6923911 < baseStart_6923911 := by decide
  rcases family_descends (prefixWord ++ tailWord_6923911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6923922 : List Nat := [3, 2, 3, 1, 4, 1, 1, 3, 1, 4]
def baseStart_6923922 : Nat := 118140960795 + 6923922 * 2 ^ 59
def prefixEnd_6923922 : Nat := 4983230072969 + 3 ^ 40 * 6923922 * 2
def baseEnd_6923922 : Nat := 1185100000079988119010823

theorem tailTrace_6923922 : CollatzResearch.WordTrace tailWord_6923922 prefixEnd_6923922 1185100000079988119010823 := by
  unfold tailWord_6923922
  simp only [CollatzResearch.WordTrace]
  refine ⟨63134045505455145144535505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168357454681213720385428013 63134045505455145144535505)
  ·
    refine ⟨47350534129091358858401629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63134045505455145144535505 47350534129091358858401629)
    ·
      refine ⟨17756450298409259571900611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47350534129091358858401629 17756450298409259571900611)
      ·
        refine ⟨26634675447613889357850917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17756450298409259571900611 26634675447613889357850917)
        ·
          refine ⟨4994001646427604254597047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26634675447613889357850917 4994001646427604254597047)
          ·
            refine ⟨7491002469641406381895571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4994001646427604254597047 7491002469641406381895571)
            ·
              refine ⟨11236503704462109572843357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7491002469641406381895571 11236503704462109572843357)
              ·
                refine ⟨4213688889173291089816259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11236503704462109572843357 4213688889173291089816259)
                ·
                  refine ⟨6320533333759936634724389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4213688889173291089816259 6320533333759936634724389)
                  ·
                    refine ⟨1185100000079988119010823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6320533333759936634724389 1185100000079988119010823)
                    ·
                      rfl

theorem cell23_6923922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_6923922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6923922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6923922 prefixEnd_6923922 := by exact prefixLift 6923922
  have htrace : WordTrace (prefixWord ++ tailWord_6923922) baseStart_6923922 baseEnd_6923922 := by
    simpa [prefixWord, tailWord_6923922, baseEnd_6923922] using wordTrace_append hprefix tailTrace_6923922
  have hstable : (prefixWord ++ tailWord_6923922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6923922).length < 2 ^ (prefixWord ++ tailWord_6923922).sum := by decide
  have hdescent : baseEnd_6923922 < baseStart_6923922 := by decide
  rcases family_descends (prefixWord ++ tailWord_6923922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6923954 : List Nat := [3, 2, 1, 1, 1, 2, 4, 2, 1, 1, 5]
def baseStart_6923954 : Nat := 118140960795 + 6923954 * 2 ^ 59
def prefixEnd_6923954 : Nat := 4983230072969 + 3 ^ 40 * 6923954 * 2
def baseEnd_6923954 : Nat := 3555316431620908231832321

theorem tailTrace_6923954 : CollatzResearch.WordTrace tailWord_6923954 prefixEnd_6923954 3555316431620908231832321 := by
  unfold tailWord_6923954
  simp only [CollatzResearch.WordTrace]
  refine ⟨63134337289426162510826729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168358232771803100028871277 63134337289426162510826729)
  ·
    refine ⟨47350752967069621883120047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63134337289426162510826729 47350752967069621883120047)
    ·
      refine ⟨71026129450604432824680071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47350752967069621883120047 71026129450604432824680071)
      ·
        refine ⟨106539194175906649237020107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71026129450604432824680071 106539194175906649237020107)
        ·
          refine ⟨159808791263859973855530161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106539194175906649237020107 159808791263859973855530161)
          ·
            refine ⟨119856593447894980391647621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159808791263859973855530161 119856593447894980391647621)
            ·
              refine ⟨22473111271480308823433929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119856593447894980391647621 22473111271480308823433929)
              ·
                refine ⟨16854833453610231617575447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22473111271480308823433929 16854833453610231617575447)
                ·
                  refine ⟨25282250180415347426363171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16854833453610231617575447 25282250180415347426363171)
                  ·
                    refine ⟨37923375270623021139544757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25282250180415347426363171 37923375270623021139544757)
                    ·
                      refine ⟨3555316431620908231832321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37923375270623021139544757 3555316431620908231832321)
                      ·
                        rfl

theorem cell23_6923954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 2, 1, 1, 5].length) (baseStart_6923954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6923954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6923954 prefixEnd_6923954 := by exact prefixLift 6923954
  have htrace : WordTrace (prefixWord ++ tailWord_6923954) baseStart_6923954 baseEnd_6923954 := by
    simpa [prefixWord, tailWord_6923954, baseEnd_6923954] using wordTrace_append hprefix tailTrace_6923954
  have hstable : (prefixWord ++ tailWord_6923954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6923954).length < 2 ^ (prefixWord ++ tailWord_6923954).sum := by decide
  have hdescent : baseEnd_6923954 < baseStart_6923954 := by decide
  rcases family_descends (prefixWord ++ tailWord_6923954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6923964 : List Nat := [2, 2, 2, 3, 1, 2, 2, 1, 1, 1, 6]
def baseStart_6923964 : Nat := 118140960795 + 6923964 * 2 ^ 59
def prefixEnd_6923964 : Nat := 4983230072969 + 3 ^ 40 * 6923964 * 2
def baseEnd_6923964 : Nat := 3555321566427453192707275

theorem tailTrace_6923964 : CollatzResearch.WordTrace tailWord_6923964 prefixEnd_6923964 3555321566427453192707275 := by
  unfold tailWord_6923964
  simp only [CollatzResearch.WordTrace]
  refine ⟨126268856943834210875585473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168358475925112281167447297 126268856943834210875585473)
  ·
    refine ⟨94701642707875658156689105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126268856943834210875585473 94701642707875658156689105)
    ·
      refine ⟨71026232030906743617516829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94701642707875658156689105 71026232030906743617516829)
      ·
        refine ⟨26634837011590028856568811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71026232030906743617516829 26634837011590028856568811)
        ·
          refine ⟨39952255517385043284853217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26634837011590028856568811 39952255517385043284853217)
          ·
            refine ⟨29964191638038782463639913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39952255517385043284853217 29964191638038782463639913)
            ·
              refine ⟨22473143728529086847729935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29964191638038782463639913 22473143728529086847729935)
              ·
                refine ⟨33709715592793630271594903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22473143728529086847729935 33709715592793630271594903)
                ·
                  refine ⟨50564573389190445407392355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33709715592793630271594903 50564573389190445407392355)
                  ·
                    refine ⟨75846860083785668111088533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50564573389190445407392355 75846860083785668111088533)
                    ·
                      refine ⟨3555321566427453192707275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75846860083785668111088533 3555321566427453192707275)
                      ·
                        rfl

theorem cell23_6923964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_6923964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6923964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6923964 prefixEnd_6923964 := by exact prefixLift 6923964
  have htrace : WordTrace (prefixWord ++ tailWord_6923964) baseStart_6923964 baseEnd_6923964 := by
    simpa [prefixWord, tailWord_6923964, baseEnd_6923964] using wordTrace_append hprefix tailTrace_6923964
  have hstable : (prefixWord ++ tailWord_6923964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6923964).length < 2 ^ (prefixWord ++ tailWord_6923964).sum := by decide
  have hdescent : baseEnd_6923964 < baseStart_6923964 := by decide
  rcases family_descends (prefixWord ++ tailWord_6923964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6923988 : List Nat := [2, 4, 1, 3, 1, 3, 1, 1, 1, 1, 5]
def baseStart_6923988 : Nat := 118140960795 + 6923988 * 2 ^ 59
def prefixEnd_6923988 : Nat := 4983230072969 + 3 ^ 40 * 6923988 * 2
def baseEnd_6923988 : Nat := 3555333889963161098807165

theorem tailTrace_6923988 : CollatzResearch.WordTrace tailWord_6923988 prefixEnd_6923988 3555333889963161098807165 := by
  unfold tailWord_6923988
  simp only [CollatzResearch.WordTrace]
  refine ⟨126269294619790736925022309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168359059493054315900029745 126269294619790736925022309)
  ·
    refine ⟨23675492741210763173441683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126269294619790736925022309 23675492741210763173441683)
    ·
      refine ⟨35513239111816144760162525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23675492741210763173441683 35513239111816144760162525)
      ·
        refine ⟨13317464666931054285060947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35513239111816144760162525 13317464666931054285060947)
        ·
          refine ⟨19976197000396581427591421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13317464666931054285060947 19976197000396581427591421)
          ·
            refine ⟨7491073875148718035346783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19976197000396581427591421 7491073875148718035346783)
            ·
              refine ⟨11236610812723077053020175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7491073875148718035346783 11236610812723077053020175)
              ·
                refine ⟨16854916219084615579530263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11236610812723077053020175 16854916219084615579530263)
                ·
                  refine ⟨25282374328626923369295395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16854916219084615579530263 25282374328626923369295395)
                  ·
                    refine ⟨37923561492940385053943093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25282374328626923369295395 37923561492940385053943093)
                    ·
                      refine ⟨3555333889963161098807165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37923561492940385053943093 3555333889963161098807165)
                      ·
                        rfl

theorem cell23_6923988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_6923988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6923988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6923988 prefixEnd_6923988 := by exact prefixLift 6923988
  have htrace : WordTrace (prefixWord ++ tailWord_6923988) baseStart_6923988 baseEnd_6923988 := by
    simpa [prefixWord, tailWord_6923988, baseEnd_6923988] using wordTrace_append hprefix tailTrace_6923988
  have hstable : (prefixWord ++ tailWord_6923988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6923988).length < 2 ^ (prefixWord ++ tailWord_6923988).sum := by decide
  have hdescent : baseEnd_6923988 < baseStart_6923988 := by decide
  rcases family_descends (prefixWord ++ tailWord_6923988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6923996 : List Nat := [2, 2, 5, 1, 3, 1, 2, 2, 1, 1, 3]
def baseStart_6923996 : Nat := 118140960795 + 6923996 * 2 ^ 59
def prefixEnd_6923996 : Nat := 4983230072969 + 3 ^ 40 * 6923996 * 2
def baseEnd_6923996 : Nat := 3555337997808397067507129

theorem tailTrace_6923996 : CollatzResearch.WordTrace tailWord_6923996 prefixEnd_6923996 3555337997808397067507129 := by
  unfold tailWord_6923996
  simp only [CollatzResearch.WordTrace]
  refine ⟨126269440511776245608167921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168359254015701660810890561 126269440511776245608167921)
  ·
    refine ⟨94702080383832184206125941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126269440511776245608167921 94702080383832184206125941)
    ·
      refine ⟨8878320035984267269324307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 94702080383832184206125941 8878320035984267269324307)
      ·
        refine ⟨13317480053976400903986461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8878320035984267269324307 13317480053976400903986461)
        ·
          refine ⟨4994055020241150338994923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13317480053976400903986461 4994055020241150338994923)
          ·
            refine ⟨7491082530361725508492385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4994055020241150338994923 7491082530361725508492385)
            ·
              refine ⟨5618311897771294131369289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7491082530361725508492385 5618311897771294131369289)
              ·
                refine ⟨4213733923328470598526967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5618311897771294131369289 4213733923328470598526967)
                ·
                  refine ⟨6320600884992705897790451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4213733923328470598526967 6320600884992705897790451)
                  ·
                    refine ⟨9480901327489058846685677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6320600884992705897790451 9480901327489058846685677)
                    ·
                      refine ⟨3555337997808397067507129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9480901327489058846685677 3555337997808397067507129)
                      ·
                        rfl

theorem cell23_6923996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_6923996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6923996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6923996 prefixEnd_6923996 := by exact prefixLift 6923996
  have htrace : WordTrace (prefixWord ++ tailWord_6923996) baseStart_6923996 baseEnd_6923996 := by
    simpa [prefixWord, tailWord_6923996, baseEnd_6923996] using wordTrace_append hprefix tailTrace_6923996
  have hstable : (prefixWord ++ tailWord_6923996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6923996).length < 2 ^ (prefixWord ++ tailWord_6923996).sum := by decide
  have hdescent : baseEnd_6923996 < baseStart_6923996 := by decide
  rcases family_descends (prefixWord ++ tailWord_6923996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6924011 : List Nat := [1, 1, 1, 1, 2, 4, 3, 2, 3, 3, 2]
def baseStart_6924011 : Nat := 118140960795 + 6924011 * 2 ^ 59
def prefixEnd_6924011 : Nat := 4983230072969 + 3 ^ 40 * 6924011 * 2
def baseEnd_6924011 : Nat := 3555345700018214508819559

theorem tailTrace_6924011 : CollatzResearch.WordTrace tailWord_6924011 prefixEnd_6924011 3555345700018214508819559 := by
  unfold tailWord_6924011
  simp only [CollatzResearch.WordTrace]
  refine ⟨252539428118498148778131887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168359618745665432518754591 252539428118498148778131887)
  ·
    refine ⟨378809142177747223167197831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252539428118498148778131887 378809142177747223167197831)
    ·
      refine ⟨568213713266620834750796747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378809142177747223167197831 568213713266620834750796747)
      ·
        refine ⟨852320569899931252126195121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 568213713266620834750796747 852320569899931252126195121)
        ·
          refine ⟨639240427424948439094646341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 852320569899931252126195121 639240427424948439094646341)
          ·
            refine ⟨119857580142177832330246189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 639240427424948439094646341 119857580142177832330246189)
            ·
              refine ⟨44946592553316687123842321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119857580142177832330246189 44946592553316687123842321)
              ·
                refine ⟨33709944414987515342881741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44946592553316687123842321 33709944414987515342881741)
                ·
                  refine ⟨12641229155620318253580653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33709944414987515342881741 12641229155620318253580653)
                  ·
                    refine ⟨4740460933357619345092745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12641229155620318253580653 4740460933357619345092745)
                    ·
                      refine ⟨3555345700018214508819559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4740460933357619345092745 3555345700018214508819559)
                      ·
                        rfl

theorem cell23_6924011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 3, 3, 2].length) (baseStart_6924011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6924011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6924011 prefixEnd_6924011 := by exact prefixLift 6924011
  have htrace : WordTrace (prefixWord ++ tailWord_6924011) baseStart_6924011 baseEnd_6924011 := by
    simpa [prefixWord, tailWord_6924011, baseEnd_6924011] using wordTrace_append hprefix tailTrace_6924011
  have hstable : (prefixWord ++ tailWord_6924011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6924011).length < 2 ^ (prefixWord ++ tailWord_6924011).sum := by decide
  have hdescent : baseEnd_6924011 < baseStart_6924011 := by decide
  rcases family_descends (prefixWord ++ tailWord_6924011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6924018 : List Nat := [3, 2, 1, 3, 1, 1, 1, 5, 2, 1, 3]
def baseStart_6924018 : Nat := 118140960795 + 6924018 * 2 ^ 59
def prefixEnd_6924018 : Nat := 4983230072969 + 3 ^ 40 * 6924018 * 2
def baseEnd_6924018 : Nat := 3555349294382795981432027

theorem tailTrace_6924018 : CollatzResearch.WordTrace tailWord_6924018 prefixEnd_6924018 3555349294382795981432027 := by
  unfold tailWord_6924018
  simp only [CollatzResearch.WordTrace]
  refine ⟨63134920857368197243409177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168359788952981859315757805 63134920857368197243409177)
  ·
    refine ⟨47351190643026147932556883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63134920857368197243409177 47351190643026147932556883)
    ·
      refine ⟨71026785964539221898835325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47351190643026147932556883 71026785964539221898835325)
      ·
        refine ⟨26635044736702208212063247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71026785964539221898835325 26635044736702208212063247)
        ·
          refine ⟨39952567105053312318094871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26635044736702208212063247 39952567105053312318094871)
          ·
            refine ⟨59928850657579968477142307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39952567105053312318094871 59928850657579968477142307)
            ·
              refine ⟨89893275986369952715713461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59928850657579968477142307 89893275986369952715713461)
              ·
                refine ⟨8427494623722183067098137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89893275986369952715713461 8427494623722183067098137)
                ·
                  refine ⟨6320620967791637300323603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8427494623722183067098137 6320620967791637300323603)
                  ·
                    refine ⟨9480931451687455950485405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6320620967791637300323603 9480931451687455950485405)
                    ·
                      refine ⟨3555349294382795981432027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9480931451687455950485405 3555349294382795981432027)
                      ·
                        rfl

theorem cell23_6924018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_6924018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6924018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6924018 prefixEnd_6924018 := by exact prefixLift 6924018
  have htrace : WordTrace (prefixWord ++ tailWord_6924018) baseStart_6924018 baseEnd_6924018 := by
    simpa [prefixWord, tailWord_6924018, baseEnd_6924018] using wordTrace_append hprefix tailTrace_6924018
  have hstable : (prefixWord ++ tailWord_6924018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6924018).length < 2 ^ (prefixWord ++ tailWord_6924018).sum := by decide
  have hdescent : baseEnd_6924018 < baseStart_6924018 := by decide
  rcases family_descends (prefixWord ++ tailWord_6924018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6924028 : List Nat := [2, 2, 2, 1, 3, 1, 2, 4, 1, 3, 2]
def baseStart_6924028 : Nat := 118140960795 + 6924028 * 2 ^ 59
def prefixEnd_6924028 : Nat := 4983230072969 + 3 ^ 40 * 6924028 * 2
def baseEnd_6924028 : Nat := 3555354429189340942306981

theorem tailTrace_6924028 : CollatzResearch.WordTrace tailWord_6924028 prefixEnd_6924028 3555354429189340942306981 := by
  unfold tailWord_6924028
  simp only [CollatzResearch.WordTrace]
  refine ⟨126270024079718280340750369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168360032106291040454333825 126270024079718280340750369)
  ·
    refine ⟨94702518059788710255562777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126270024079718280340750369 94702518059788710255562777)
    ·
      refine ⟨71026888544841532691672083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94702518059788710255562777 71026888544841532691672083)
      ·
        refine ⟨106540332817262299037508125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71026888544841532691672083 106540332817262299037508125)
        ·
          refine ⟨39952624806473362139065547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106540332817262299037508125 39952624806473362139065547)
          ·
            refine ⟨59928937209710043208598321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39952624806473362139065547 59928937209710043208598321)
            ·
              refine ⟨44946702907282532406448741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59928937209710043208598321 44946702907282532406448741)
              ·
                refine ⟨8427506795115474826209139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44946702907282532406448741 8427506795115474826209139)
                ·
                  refine ⟨12641260192673212239313709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8427506795115474826209139 12641260192673212239313709)
                  ·
                    refine ⟨4740472572252454589742641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12641260192673212239313709 4740472572252454589742641)
                    ·
                      refine ⟨3555354429189340942306981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4740472572252454589742641 3555354429189340942306981)
                      ·
                        rfl

theorem cell23_6924028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 4, 1, 3, 2].length) (baseStart_6924028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6924028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6924028 prefixEnd_6924028 := by exact prefixLift 6924028
  have htrace : WordTrace (prefixWord ++ tailWord_6924028) baseStart_6924028 baseEnd_6924028 := by
    simpa [prefixWord, tailWord_6924028, baseEnd_6924028] using wordTrace_append hprefix tailTrace_6924028
  have hstable : (prefixWord ++ tailWord_6924028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6924028).length < 2 ^ (prefixWord ++ tailWord_6924028).sum := by decide
  have hdescent : baseEnd_6924028 < baseStart_6924028 := by decide
  rcases family_descends (prefixWord ++ tailWord_6924028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6924044 : List Nat := [2, 2, 1, 2, 2, 1, 2, 3, 2, 1, 5]
def baseStart_6924044 : Nat := 118140960795 + 6924044 * 2 ^ 59
def prefixEnd_6924044 : Nat := 4983230072969 + 3 ^ 40 * 6924044 * 2
def baseEnd_6924044 : Nat := 3555362644879812879706907

theorem tailTrace_6924044 : CollatzResearch.WordTrace tailWord_6924044 prefixEnd_6924044 3555362644879812879706907 := by
  unfold tailWord_6924044
  simp only [CollatzResearch.WordTrace]
  refine ⟨126270315863689297707041593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168360421151585730276055457 126270315863689297707041593)
  ·
    refine ⟨94702736897766973280281195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126270315863689297707041593 94702736897766973280281195)
    ·
      refine ⟨142054105346650459920421793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94702736897766973280281195 142054105346650459920421793)
      ·
        refine ⟨106540579009987844940316345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142054105346650459920421793 106540579009987844940316345)
        ·
          refine ⟨79905434257490883705237259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106540579009987844940316345 79905434257490883705237259)
          ·
            refine ⟨119858151386236325557855889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79905434257490883705237259 119858151386236325557855889)
            ·
              refine ⟨89893613539677244168391917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119858151386236325557855889 89893613539677244168391917)
              ·
                refine ⟨33710105077378966563146969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89893613539677244168391917 33710105077378966563146969)
                ·
                  refine ⟨25282578808034224922360227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33710105077378966563146969 25282578808034224922360227)
                  ·
                    refine ⟨37923868212051337383540341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25282578808034224922360227 37923868212051337383540341)
                    ·
                      refine ⟨3555362644879812879706907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37923868212051337383540341 3555362644879812879706907)
                      ·
                        rfl

theorem cell23_6924044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 2, 1, 5].length) (baseStart_6924044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6924044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6924044 prefixEnd_6924044 := by exact prefixLift 6924044
  have htrace : WordTrace (prefixWord ++ tailWord_6924044) baseStart_6924044 baseEnd_6924044 := by
    simpa [prefixWord, tailWord_6924044, baseEnd_6924044] using wordTrace_append hprefix tailTrace_6924044
  have hstable : (prefixWord ++ tailWord_6924044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6924044).length < 2 ^ (prefixWord ++ tailWord_6924044).sum := by decide
  have hdescent : baseEnd_6924044 < baseStart_6924044 := by decide
  rcases family_descends (prefixWord ++ tailWord_6924044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6924144 : List Nat := [2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 6]
def baseStart_6924144 : Nat := 118140960795 + 6924144 * 2 ^ 59
def prefixEnd_6924144 : Nat := 4983230072969 + 3 ^ 40 * 6924144 * 2
def baseEnd_6924144 : Nat := 3555413992945262488456447

theorem tailTrace_6924144 : CollatzResearch.WordTrace tailWord_6924144 prefixEnd_6924144 3555413992945262488456447 := by
  unfold tailWord_6924144
  simp only [CollatzResearch.WordTrace]
  refine ⟨126272139513508156246361743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168362852684677541661815657 126272139513508156246361743)
  ·
    refine ⟨189408209270262234369542615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126272139513508156246361743 189408209270262234369542615)
    ·
      refine ⟨284112313905393351554313923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189408209270262234369542615 284112313905393351554313923)
      ·
        refine ⟨426168470858090027331470885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284112313905393351554313923 426168470858090027331470885)
        ·
          refine ⟨79906588285891880124650791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 426168470858090027331470885 79906588285891880124650791)
          ·
            refine ⟨119859882428837820186976187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79906588285891880124650791 119859882428837820186976187)
            ·
              refine ⟨179789823643256730280464281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119859882428837820186976187 179789823643256730280464281)
              ·
                refine ⟨134842367732442547710348211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179789823643256730280464281 134842367732442547710348211)
                ·
                  refine ⟨202263551598663821565522317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134842367732442547710348211 202263551598663821565522317)
                  ·
                    refine ⟨75848831849498933087070869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 202263551598663821565522317 75848831849498933087070869)
                    ·
                      refine ⟨3555413992945262488456447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75848831849498933087070869 3555413992945262488456447)
                      ·
                        rfl

theorem cell23_6924144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 6].length) (baseStart_6924144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6924144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6924144 prefixEnd_6924144 := by exact prefixLift 6924144
  have htrace : WordTrace (prefixWord ++ tailWord_6924144) baseStart_6924144 baseEnd_6924144 := by
    simpa [prefixWord, tailWord_6924144, baseEnd_6924144] using wordTrace_append hprefix tailTrace_6924144
  have hstable : (prefixWord ++ tailWord_6924144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6924144).length < 2 ^ (prefixWord ++ tailWord_6924144).sum := by decide
  have hdescent : baseEnd_6924144 < baseStart_6924144 := by decide
  rcases family_descends (prefixWord ++ tailWord_6924144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6924154 : List Nat := [3, 1, 1, 1, 1, 1, 4, 1, 10]
def baseStart_6924154 : Nat := 118140960795 + 6924154 * 2 ^ 59
def prefixEnd_6924154 : Nat := 4983230072969 + 3 ^ 40 * 6924154 * 2
def baseEnd_6924154 : Nat := 395046569750200827703489

theorem tailTrace_6924154 : CollatzResearch.WordTrace tailWord_6924154 prefixEnd_6924154 395046569750200827703489 := by
  unfold tailWord_6924154
  simp only [CollatzResearch.WordTrace]
  refine ⟨63136160939245021050146879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168363095837986722800391677 63136160939245021050146879)
  ·
    refine ⟨94704241408867531575220319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63136160939245021050146879 94704241408867531575220319)
    ·
      refine ⟨142056362113301297362830479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94704241408867531575220319 142056362113301297362830479)
      ·
        refine ⟨213084543169951946044245719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142056362113301297362830479 213084543169951946044245719)
        ·
          refine ⟨319626814754927919066368579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213084543169951946044245719 319626814754927919066368579)
          ·
            refine ⟨479440222132391878599552869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319626814754927919066368579 479440222132391878599552869)
            ·
              refine ⟨89895041649823477237416163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 479440222132391878599552869 89895041649823477237416163)
              ·
                refine ⟨134842562474735215856124245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89895041649823477237416163 134842562474735215856124245)
                ·
                  refine ⟨395046569750200827703489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 134842562474735215856124245 395046569750200827703489)
                  ·
                    rfl

theorem cell23_6924154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 10].length) (baseStart_6924154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6924154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6924154 prefixEnd_6924154 := by exact prefixLift 6924154
  have htrace : WordTrace (prefixWord ++ tailWord_6924154) baseStart_6924154 baseEnd_6924154 := by
    simpa [prefixWord, tailWord_6924154, baseEnd_6924154] using wordTrace_append hprefix tailTrace_6924154
  have hstable : (prefixWord ++ tailWord_6924154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6924154).length < 2 ^ (prefixWord ++ tailWord_6924154).sum := by decide
  have hdescent : baseEnd_6924154 < baseStart_6924154 := by decide
  rcases family_descends (prefixWord ++ tailWord_6924154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6924188 : List Nat := [2, 2, 3, 3, 1, 1, 2, 3, 6]
def baseStart_6924188 : Nat := 118140960795 + 6924188 * 2 ^ 59
def prefixEnd_6924188 : Nat := 4983230072969 + 3 ^ 40 * 6924188 * 2
def baseEnd_6924188 : Nat := 395048509566006701811805

theorem tailTrace_6924188 : CollatzResearch.WordTrace tailWord_6924188 prefixEnd_6924188 395048509566006701811805 := by
  unfold tailWord_6924188
  simp only [CollatzResearch.WordTrace]
  refine ⟨126272941919428454003662609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168363922559237938671550145 126272941919428454003662609)
  ·
    refine ⟨94704706439571340502746957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126272941919428454003662609 94704706439571340502746957)
    ·
      refine ⟨35514264914839252688530109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94704706439571340502746957 35514264914839252688530109)
      ·
        refine ⟨13317849343064719758198791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35514264914839252688530109 13317849343064719758198791)
        ·
          refine ⟨19976774014597079637298187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13317849343064719758198791 19976774014597079637298187)
          ·
            refine ⟨29965161021895619455947281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19976774014597079637298187 29965161021895619455947281)
            ·
              refine ⟨22473870766421714591960461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29965161021895619455947281 22473870766421714591960461)
              ·
                refine ⟨8427701537408142971985173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22473870766421714591960461 8427701537408142971985173)
                ·
                  refine ⟨395048509566006701811805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8427701537408142971985173 395048509566006701811805)
                  ·
                    rfl

theorem cell23_6924188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 3, 6].length) (baseStart_6924188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6924188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6924188 prefixEnd_6924188 := by exact prefixLift 6924188
  have htrace : WordTrace (prefixWord ++ tailWord_6924188) baseStart_6924188 baseEnd_6924188 := by
    simpa [prefixWord, tailWord_6924188, baseEnd_6924188] using wordTrace_append hprefix tailTrace_6924188
  have hstable : (prefixWord ++ tailWord_6924188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6924188).length < 2 ^ (prefixWord ++ tailWord_6924188).sum := by decide
  have hdescent : baseEnd_6924188 < baseStart_6924188 := by decide
  rcases family_descends (prefixWord ++ tailWord_6924188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6924232 : List Nat := [2, 1, 3, 1, 4, 1, 2, 4, 1, 1, 3]
def baseStart_6924232 : Nat := 118140960795 + 6924232 * 2 ^ 59
def prefixEnd_6924232 : Nat := 4983230072969 + 3 ^ 40 * 6924232 * 2
def baseEnd_6924232 : Nat := 3555459179242858144156043

theorem tailTrace_6924232 : CollatzResearch.WordTrace tailWord_6924232 prefixEnd_6924232 3555459179242858144156043 := by
  unfold tailWord_6924232
  simp only [CollatzResearch.WordTrace]
  refine ⟨126273744325348751760963475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168364992433798335681284633 126273744325348751760963475)
  ·
    refine ⟨189410616488023127641445213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126273744325348751760963475 189410616488023127641445213)
    ·
      refine ⟨71028981183008672865541955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189410616488023127641445213 71028981183008672865541955)
      ·
        refine ⟨106543471774513009298312933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71028981183008672865541955 106543471774513009298312933)
        ·
          refine ⟨19976900957721189243433675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106543471774513009298312933 19976900957721189243433675)
          ·
            refine ⟨29965351436581783865150513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19976900957721189243433675 29965351436581783865150513)
            ·
              refine ⟨22474013577436337898862885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29965351436581783865150513 22474013577436337898862885)
              ·
                refine ⟨4213877545769313356036791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22474013577436337898862885 4213877545769313356036791)
                ·
                  refine ⟨6320816318653970034055187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4213877545769313356036791 6320816318653970034055187)
                  ·
                    refine ⟨9481224477980955051082781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6320816318653970034055187 9481224477980955051082781)
                    ·
                      refine ⟨3555459179242858144156043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9481224477980955051082781 3555459179242858144156043)
                      ·
                        rfl

theorem cell23_6924232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 4, 1, 1, 3].length) (baseStart_6924232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6924232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6924232 prefixEnd_6924232 := by exact prefixLift 6924232
  have htrace : WordTrace (prefixWord ++ tailWord_6924232) baseStart_6924232 baseEnd_6924232 := by
    simpa [prefixWord, tailWord_6924232, baseEnd_6924232] using wordTrace_append hprefix tailTrace_6924232
  have hstable : (prefixWord ++ tailWord_6924232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6924232).length < 2 ^ (prefixWord ++ tailWord_6924232).sum := by decide
  have hdescent : baseEnd_6924232 < baseStart_6924232 := by decide
  rcases family_descends (prefixWord ++ tailWord_6924232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6924241 : List Nat := [1, 2, 2, 1, 2, 1, 2, 1, 2, 6, 3]
def baseStart_6924241 : Nat := 118140960795 + 6924241 * 2 ^ 59
def prefixEnd_6924241 : Nat := 4983230072969 + 3 ^ 40 * 6924241 * 2
def baseEnd_6924241 : Nat := 3555463800568748608943501

theorem tailTrace_6924241 : CollatzResearch.WordTrace tailWord_6924241 prefixEnd_6924241 3555463800568748608943501 := by
  unfold tailWord_6924241
  simp only [CollatzResearch.WordTrace]
  refine ⟨252547816907664898059004577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168365211271776598706003051 252547816907664898059004577)
  ·
    refine ⟨189410862680748673544253433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252547816907664898059004577 189410862680748673544253433)
    ·
      refine ⟨142058147010561505158190075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189410862680748673544253433 142058147010561505158190075)
      ·
        refine ⟨213087220515842257737285113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142058147010561505158190075 213087220515842257737285113)
        ·
          refine ⟨159815415386881693302963835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213087220515842257737285113 159815415386881693302963835)
          ·
            refine ⟨239723123080322539954445753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159815415386881693302963835 239723123080322539954445753)
            ·
              refine ⟨179792342310241904965834315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 239723123080322539954445753 179792342310241904965834315)
              ·
                refine ⟨269688513465362857448751473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179792342310241904965834315 269688513465362857448751473)
                ·
                  refine ⟨202266385099022143086563605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 269688513465362857448751473 202266385099022143086563605)
                  ·
                    refine ⟨9481236801516662957182669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 202266385099022143086563605 9481236801516662957182669)
                    ·
                      refine ⟨3555463800568748608943501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9481236801516662957182669 3555463800568748608943501)
                      ·
                        rfl

theorem cell23_6924241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 6, 3].length) (baseStart_6924241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6924241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6924241 prefixEnd_6924241 := by exact prefixLift 6924241
  have htrace : WordTrace (prefixWord ++ tailWord_6924241) baseStart_6924241 baseEnd_6924241 := by
    simpa [prefixWord, tailWord_6924241, baseEnd_6924241] using wordTrace_append hprefix tailTrace_6924241
  have hstable : (prefixWord ++ tailWord_6924241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6924241).length < 2 ^ (prefixWord ++ tailWord_6924241).sum := by decide
  have hdescent : baseEnd_6924241 < baseStart_6924241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6924241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6924255 : List Nat := [1, 1, 2, 3, 4, 2, 2, 2, 1, 1, 4]
def baseStart_6924255 : Nat := 118140960795 + 6924255 * 2 ^ 59
def prefixEnd_6924255 : Nat := 4983230072969 + 3 ^ 40 * 6924255 * 2
def baseEnd_6924255 : Nat := 3555470989297911554168437

theorem tailTrace_6924255 : CollatzResearch.WordTrace tailWord_6924255 prefixEnd_6924255 3555470989297911554168437 := by
  unfold tailWord_6924255
  simp only [CollatzResearch.WordTrace]
  refine ⟨252548327529614178450014219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168365551686409452300009479 252548327529614178450014219)
  ·
    refine ⟨378822491294421267675021329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252548327529614178450014219 378822491294421267675021329)
    ·
      refine ⟨284116868470815950756265997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 378822491294421267675021329 284116868470815950756265997)
      ·
        refine ⟨106543825676555981533599749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 284116868470815950756265997 106543825676555981533599749)
        ·
          refine ⟨19976967314354246537549953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106543825676555981533599749 19976967314354246537549953)
          ·
            refine ⟨14982725485765684903162465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19976967314354246537549953 14982725485765684903162465)
            ·
              refine ⟨11237044114324263677371849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14982725485765684903162465 11237044114324263677371849)
              ·
                refine ⟨8427783085743197758028887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11237044114324263677371849 8427783085743197758028887)
                ·
                  refine ⟨12641674628614796637043331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8427783085743197758028887 12641674628614796637043331)
                  ·
                    refine ⟨18962511942922194955564997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12641674628614796637043331 18962511942922194955564997)
                    ·
                      refine ⟨3555470989297911554168437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18962511942922194955564997 3555470989297911554168437)
                      ·
                        rfl

theorem cell23_6924255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 2, 1, 1, 4].length) (baseStart_6924255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6924255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6924255 prefixEnd_6924255 := by exact prefixLift 6924255
  have htrace : WordTrace (prefixWord ++ tailWord_6924255) baseStart_6924255 baseEnd_6924255 := by
    simpa [prefixWord, tailWord_6924255, baseEnd_6924255] using wordTrace_append hprefix tailTrace_6924255
  have hstable : (prefixWord ++ tailWord_6924255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6924255).length < 2 ^ (prefixWord ++ tailWord_6924255).sum := by decide
  have hdescent : baseEnd_6924255 < baseStart_6924255 := by decide
  rcases family_descends (prefixWord ++ tailWord_6924255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6924309 : List Nat := [1, 3, 2, 1, 6, 1, 1, 2, 1, 2, 3]
def baseStart_6924309 : Nat := 118140960795 + 6924309 * 2 ^ 59
def prefixEnd_6924309 : Nat := 4983230072969 + 3 ^ 40 * 6924309 * 2
def baseEnd_6924309 : Nat := 3555498717253254342893189

theorem tailTrace_6924309 : CollatzResearch.WordTrace tailWord_6924309 prefixEnd_6924309 3555498717253254342893189 := by
  unfold tailWord_6924309
  simp only [CollatzResearch.WordTrace]
  refine ⟨252550297071418545672479981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168366864714279030448319987 252550297071418545672479981)
  ·
    refine ⟨94706361401781954627179993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252550297071418545672479981 94706361401781954627179993)
    ·
      refine ⟨71029771051336465970384995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94706361401781954627179993 71029771051336465970384995)
      ·
        refine ⟨106544656577004698955577493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71029771051336465970384995 106544656577004698955577493)
        ·
          refine ⟨4994280777047095263542695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 106544656577004698955577493 4994280777047095263542695)
          ·
            refine ⟨7491421165570642895314043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4994280777047095263542695 7491421165570642895314043)
            ·
              refine ⟨11237131748355964342971065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7491421165570642895314043 11237131748355964342971065)
              ·
                refine ⟨8427848811266973257228299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11237131748355964342971065 8427848811266973257228299)
                ·
                  refine ⟨12641773216900459885842449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8427848811266973257228299 12641773216900459885842449)
                  ·
                    refine ⟨9481329912675344914381837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12641773216900459885842449 9481329912675344914381837)
                    ·
                      refine ⟨3555498717253254342893189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9481329912675344914381837 3555498717253254342893189)
                      ·
                        rfl

theorem cell23_6924309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 2, 1, 2, 3].length) (baseStart_6924309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6924309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6924309 prefixEnd_6924309 := by exact prefixLift 6924309
  have htrace : WordTrace (prefixWord ++ tailWord_6924309) baseStart_6924309 baseEnd_6924309 := by
    simpa [prefixWord, tailWord_6924309, baseEnd_6924309] using wordTrace_append hprefix tailTrace_6924309
  have hstable : (prefixWord ++ tailWord_6924309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6924309).length < 2 ^ (prefixWord ++ tailWord_6924309).sum := by decide
  have hdescent : baseEnd_6924309 < baseStart_6924309 := by decide
  rcases family_descends (prefixWord ++ tailWord_6924309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6924315 : List Nat := [1, 1, 1, 1, 1, 1, 3, 8, 1, 3, 2]
def baseStart_6924315 : Nat := 118140960795 + 6924315 * 2 ^ 59
def prefixEnd_6924315 : Nat := 4983230072969 + 3 ^ 40 * 6924315 * 2
def baseEnd_6924315 : Nat := 3555501798137181319418161

theorem tailTrace_6924315 : CollatzResearch.WordTrace tailWord_6924315 prefixEnd_6924315 3555501798137181319418161 := by
  unfold tailWord_6924315
  simp only [CollatzResearch.WordTrace]
  refine ⟨252550515909396808697198399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168367010606264539131465599 252550515909396808697198399)
  ·
    refine ⟨378825773864095213045797599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252550515909396808697198399 378825773864095213045797599)
    ·
      refine ⟨568238660796142819568696399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378825773864095213045797599 568238660796142819568696399)
      ·
        refine ⟨852357991194214229353044599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 568238660796142819568696399 852357991194214229353044599)
        ·
          refine ⟨1278536986791321344029566899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 852357991194214229353044599 1278536986791321344029566899)
          ·
            refine ⟨1917805480186982016044350349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1278536986791321344029566899 1917805480186982016044350349)
            ·
              refine ⟨719177055070118256016631381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1917805480186982016044350349 719177055070118256016631381)
              ·
                refine ⟨8427856114102948312694899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 719177055070118256016631381 8427856114102948312694899)
                ·
                  refine ⟨12641784171154422469042349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8427856114102948312694899 12641784171154422469042349)
                  ·
                    refine ⟨4740669064182908425890881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12641784171154422469042349 4740669064182908425890881)
                    ·
                      refine ⟨3555501798137181319418161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4740669064182908425890881 3555501798137181319418161)
                      ·
                        rfl

theorem cell23_6924315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 8, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 8, 1, 3, 2].length) (baseStart_6924315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6924315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6924315 prefixEnd_6924315 := by exact prefixLift 6924315
  have htrace : WordTrace (prefixWord ++ tailWord_6924315) baseStart_6924315 baseEnd_6924315 := by
    simpa [prefixWord, tailWord_6924315, baseEnd_6924315] using wordTrace_append hprefix tailTrace_6924315
  have hstable : (prefixWord ++ tailWord_6924315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6924315).length < 2 ^ (prefixWord ++ tailWord_6924315).sum := by decide
  have hdescent : baseEnd_6924315 < baseStart_6924315 := by decide
  rcases family_descends (prefixWord ++ tailWord_6924315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6924331 : List Nat := [1, 1, 1, 1, 2, 1, 4, 3, 1, 3, 5]
def baseStart_6924331 : Nat := 118140960795 + 6924331 * 2 ^ 59
def prefixEnd_6924331 : Nat := 4983230072969 + 3 ^ 40 * 6924331 * 2
def baseEnd_6924331 : Nat := 3555510013827653256818087

theorem tailTrace_6924331 : CollatzResearch.WordTrace tailWord_6924331 prefixEnd_6924331 3555510013827653256818087 := by
  unfold tailWord_6924331
  simp only [CollatzResearch.WordTrace]
  refine ⟨252551099477338843429780847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168367399651559228953187231 252551099477338843429780847)
  ·
    refine ⟨378826649216008265144671271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252551099477338843429780847 378826649216008265144671271)
    ·
      refine ⟨568239973824012397717006907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378826649216008265144671271 568239973824012397717006907)
      ·
        refine ⟨852359960736018596575510361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 568239973824012397717006907 852359960736018596575510361)
        ·
          refine ⟨639269970552013947431632771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 852359960736018596575510361 639269970552013947431632771)
          ·
            refine ⟨958904955828020921147449157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 639269970552013947431632771 958904955828020921147449157)
            ·
              refine ⟨179794679217753922715146717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 958904955828020921147449157 179794679217753922715146717)
              ·
                refine ⟨67423004706657721018180019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 179794679217753922715146717 67423004706657721018180019)
                ·
                  refine ⟨101134507059986581527270029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67423004706657721018180019 101134507059986581527270029)
                  ·
                    refine ⟨37925440147494968072726261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 101134507059986581527270029 37925440147494968072726261)
                    ·
                      refine ⟨3555510013827653256818087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37925440147494968072726261 3555510013827653256818087)
                      ·
                        rfl

theorem cell23_6924331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 3, 5].length) (baseStart_6924331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6924331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6924331 prefixEnd_6924331 := by exact prefixLift 6924331
  have htrace : WordTrace (prefixWord ++ tailWord_6924331) baseStart_6924331 baseEnd_6924331 := by
    simpa [prefixWord, tailWord_6924331, baseEnd_6924331] using wordTrace_append hprefix tailTrace_6924331
  have hstable : (prefixWord ++ tailWord_6924331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6924331).length < 2 ^ (prefixWord ++ tailWord_6924331).sum := by decide
  have hdescent : baseEnd_6924331 < baseStart_6924331 := by decide
  rcases family_descends (prefixWord ++ tailWord_6924331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6924340 : List Nat := [2, 5, 1, 2, 2, 2, 2, 2, 1, 2, 2]
def baseStart_6924340 : Nat := 118140960795 + 6924340 * 2 ^ 59
def prefixEnd_6924340 : Nat := 4983230072969 + 3 ^ 40 * 6924340 * 2
def baseEnd_6924340 : Nat := 3555514635153543721605547

theorem tailTrace_6924340 : CollatzResearch.WordTrace tailWord_6924340 prefixEnd_6924340 3555514635153543721605547 := by
  unfold tailWord_6924340
  simp only [CollatzResearch.WordTrace]
  refine ⟨126275713867153118983429237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168367618489537491977905649 126275713867153118983429237)
  ·
    refine ⟨11838348175045604904696491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 126275713867153118983429237 11838348175045604904696491)
    ·
      refine ⟨17757522262568407357044737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11838348175045604904696491 17757522262568407357044737)
      ·
        refine ⟨13318141696926305517783553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17757522262568407357044737 13318141696926305517783553)
        ·
          refine ⟨9988606272694729138337665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13318141696926305517783553 9988606272694729138337665)
          ·
            refine ⟨7491454704521046853753249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9988606272694729138337665 7491454704521046853753249)
            ·
              refine ⟨5618591028390785140314937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7491454704521046853753249 5618591028390785140314937)
              ·
                refine ⟨4213943271293088855236203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5618591028390785140314937 4213943271293088855236203)
                ·
                  refine ⟨6320914906939633282854305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4213943271293088855236203 6320914906939633282854305)
                  ·
                    refine ⟨4740686180204724962140729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6320914906939633282854305 4740686180204724962140729)
                    ·
                      refine ⟨3555514635153543721605547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4740686180204724962140729 3555514635153543721605547)
                      ·
                        rfl

theorem cell23_6924340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_6924340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6924340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6924340 prefixEnd_6924340 := by exact prefixLift 6924340
  have htrace : WordTrace (prefixWord ++ tailWord_6924340) baseStart_6924340 baseEnd_6924340 := by
    simpa [prefixWord, tailWord_6924340, baseEnd_6924340] using wordTrace_append hprefix tailTrace_6924340
  have hstable : (prefixWord ++ tailWord_6924340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6924340).length < 2 ^ (prefixWord ++ tailWord_6924340).sum := by decide
  have hdescent : baseEnd_6924340 < baseStart_6924340 := by decide
  rcases family_descends (prefixWord ++ tailWord_6924340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6924348 : List Nat := [2, 2, 2, 2, 2, 1, 1, 1, 1, 6, 3]
def baseStart_6924348 : Nat := 118140960795 + 6924348 * 2 ^ 59
def prefixEnd_6924348 : Nat := 4983230072969 + 3 ^ 40 * 6924348 * 2
def baseEnd_6924348 : Nat := 3555518742998779690305509

theorem tailTrace_6924348 : CollatzResearch.WordTrace tailWord_6924348 prefixEnd_6924348 3555518742998779690305509 := by
  unfold tailWord_6924348
  simp only [CollatzResearch.WordTrace]
  refine ⟨126275859759138627666574849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168367813012184836888766465 126275859759138627666574849)
  ·
    refine ⟨94706894819353970749931137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126275859759138627666574849 94706894819353970749931137)
    ·
      refine ⟨71030171114515478062448353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94706894819353970749931137 71030171114515478062448353)
      ·
        refine ⟨53272628335886608546836265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71030171114515478062448353 53272628335886608546836265)
        ·
          refine ⟨39954471251914956410127199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53272628335886608546836265 39954471251914956410127199)
          ·
            refine ⟨59931706877872434615190799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39954471251914956410127199 59931706877872434615190799)
            ·
              refine ⟨89897560316808651922786199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59931706877872434615190799 89897560316808651922786199)
              ·
                refine ⟨134846340475212977884179299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89897560316808651922786199 134846340475212977884179299)
                ·
                  refine ⟨202269510712819466826268949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134846340475212977884179299 202269510712819466826268949)
                  ·
                    refine ⟨9481383314663412507481357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 202269510712819466826268949 9481383314663412507481357)
                    ·
                      refine ⟨3555518742998779690305509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9481383314663412507481357 3555518742998779690305509)
                      ·
                        rfl

theorem cell23_6924348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 1, 6, 3].length) (baseStart_6924348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6924348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6924348 prefixEnd_6924348 := by exact prefixLift 6924348
  have htrace : WordTrace (prefixWord ++ tailWord_6924348) baseStart_6924348 baseEnd_6924348 := by
    simpa [prefixWord, tailWord_6924348, baseEnd_6924348] using wordTrace_append hprefix tailTrace_6924348
  have hstable : (prefixWord ++ tailWord_6924348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6924348).length < 2 ^ (prefixWord ++ tailWord_6924348).sum := by decide
  have hdescent : baseEnd_6924348 < baseStart_6924348 := by decide
  rcases family_descends (prefixWord ++ tailWord_6924348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6924365 : List Nat := [1, 6, 1, 1, 1, 1, 1, 2, 2, 4, 3]
def baseStart_6924365 : Nat := 118140960795 + 6924365 * 2 ^ 59
def prefixEnd_6924365 : Nat := 4983230072969 + 3 ^ 40 * 6924365 * 2
def baseEnd_6924365 : Nat := 3555527472169906123792931

theorem tailTrace_6924365 : CollatzResearch.WordTrace tailWord_6924365 prefixEnd_6924365 3555527472169906123792931 := by
  unfold tailWord_6924365
  simp only [CollatzResearch.WordTrace]
  refine ⟨252552339559215667236518549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168368226372810444824345699 252552339559215667236518549)
  ·
    refine ⟨11838390916838234401711807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 252552339559215667236518549 11838390916838234401711807)
    ·
      refine ⟨17757586375257351602567711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11838390916838234401711807 17757586375257351602567711)
      ·
        refine ⟨26636379562886027403851567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17757586375257351602567711 26636379562886027403851567)
        ·
          refine ⟨39954569344329041105777351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26636379562886027403851567 39954569344329041105777351)
          ·
            refine ⟨59931854016493561658666027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39954569344329041105777351 59931854016493561658666027)
            ·
              refine ⟨89897781024740342487999041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59931854016493561658666027 89897781024740342487999041)
              ·
                refine ⟨67423335768555256865999281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89897781024740342487999041 67423335768555256865999281)
                ·
                  refine ⟨50567501826416442649499461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67423335768555256865999281 50567501826416442649499461)
                  ·
                    refine ⟨9481406592453082996781149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50567501826416442649499461 9481406592453082996781149)
                    ·
                      refine ⟨3555527472169906123792931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9481406592453082996781149 3555527472169906123792931)
                      ·
                        rfl

theorem cell23_6924365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_6924365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6924365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6924365 prefixEnd_6924365 := by exact prefixLift 6924365
  have htrace : WordTrace (prefixWord ++ tailWord_6924365) baseStart_6924365 baseEnd_6924365 := by
    simpa [prefixWord, tailWord_6924365, baseEnd_6924365] using wordTrace_append hprefix tailTrace_6924365
  have hstable : (prefixWord ++ tailWord_6924365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6924365).length < 2 ^ (prefixWord ++ tailWord_6924365).sum := by decide
  have hdescent : baseEnd_6924365 < baseStart_6924365 := by decide
  rcases family_descends (prefixWord ++ tailWord_6924365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6924371 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 6]
def baseStart_6924371 : Nat := 118140960795 + 6924371 * 2 ^ 59
def prefixEnd_6924371 : Nat := 4983230072969 + 3 ^ 40 * 6924371 * 2
def baseEnd_6924371 : Nat := 3555530553053833100317903

theorem tailTrace_6924371 : CollatzResearch.WordTrace tailWord_6924371 prefixEnd_6924371 3555530553053833100317903 := by
  unfold tailWord_6924371
  simp only [CollatzResearch.WordTrace]
  refine ⟨252552558397193930261236967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168368372264795953507491311 252552558397193930261236967)
  ·
    refine ⟨378828837595790895391855451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252552558397193930261236967 378828837595790895391855451)
    ·
      refine ⟨568243256393686343087783177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378828837595790895391855451 568243256393686343087783177)
      ·
        refine ⟨426182442295264757315837383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 568243256393686343087783177 426182442295264757315837383)
        ·
          refine ⟨639273663442897135973756075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426182442295264757315837383 639273663442897135973756075)
          ·
            refine ⟨958910495164345703960634113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 639273663442897135973756075 958910495164345703960634113)
            ·
              refine ⟨719182871373259277970475585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 958910495164345703960634113 719182871373259277970475585)
              ·
                refine ⟨539387153529944458477856689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 719182871373259277970475585 539387153529944458477856689)
                ·
                  refine ⟨404540365147458343858392517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 539387153529944458477856689 404540365147458343858392517)
                  ·
                    refine ⟨75851318465148439473448597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 404540365147458343858392517 75851318465148439473448597)
                    ·
                      refine ⟨3555530553053833100317903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75851318465148439473448597 3555530553053833100317903)
                      ·
                        rfl

theorem cell23_6924371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 6].length) (baseStart_6924371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6924371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6924371 prefixEnd_6924371 := by exact prefixLift 6924371
  have htrace : WordTrace (prefixWord ++ tailWord_6924371) baseStart_6924371 baseEnd_6924371 := by
    simpa [prefixWord, tailWord_6924371, baseEnd_6924371] using wordTrace_append hprefix tailTrace_6924371
  have hstable : (prefixWord ++ tailWord_6924371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6924371).length < 2 ^ (prefixWord ++ tailWord_6924371).sum := by decide
  have hdescent : baseEnd_6924371 < baseStart_6924371 := by decide
  rcases family_descends (prefixWord ++ tailWord_6924371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6924378 : List Nat := [3, 1, 1, 2, 1, 1, 3, 2, 1, 5, 3]
def baseStart_6924378 : Nat := 118140960795 + 6924378 * 2 ^ 59
def prefixEnd_6924378 : Nat := 4983230072969 + 3 ^ 40 * 6924378 * 2
def baseEnd_6924378 : Nat := 3555534147418414572930371

theorem tailTrace_6924378 : CollatzResearch.WordTrace tailWord_6924378 prefixEnd_6924378 3555534147418414572930371 := by
  unfold tailWord_6924378
  simp only [CollatzResearch.WordTrace]
  refine ⟨63138203427042142614185447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168368542472112380304494525 63138203427042142614185447)
  ·
    refine ⟨94707305140563213921278171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63138203427042142614185447 94707305140563213921278171)
    ·
      refine ⟨142060957710844820881917257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94707305140563213921278171 142060957710844820881917257)
      ·
        refine ⟨106545718283133615661437943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142060957710844820881917257 106545718283133615661437943)
        ·
          refine ⟨159818577424700423492156915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106545718283133615661437943 159818577424700423492156915)
          ·
            refine ⟨239727866137050635238235373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159818577424700423492156915 239727866137050635238235373)
            ·
              refine ⟨89897949801393988214338265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 239727866137050635238235373 89897949801393988214338265)
              ·
                refine ⟨67423462351045491160753699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89897949801393988214338265 67423462351045491160753699)
                ·
                  refine ⟨101135193526568236741130549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67423462351045491160753699 101135193526568236741130549)
                  ·
                    refine ⟨9481424393115772194480989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 101135193526568236741130549 9481424393115772194480989)
                    ·
                      refine ⟨3555534147418414572930371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9481424393115772194480989 3555534147418414572930371)
                      ·
                        rfl

theorem cell23_6924378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 1, 5, 3].length) (baseStart_6924378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6924378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6924378 prefixEnd_6924378 := by exact prefixLift 6924378
  have htrace : WordTrace (prefixWord ++ tailWord_6924378) baseStart_6924378 baseEnd_6924378 := by
    simpa [prefixWord, tailWord_6924378, baseEnd_6924378] using wordTrace_append hprefix tailTrace_6924378
  have hstable : (prefixWord ++ tailWord_6924378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6924378).length < 2 ^ (prefixWord ++ tailWord_6924378).sum := by decide
  have hdescent : baseEnd_6924378 < baseStart_6924378 := by decide
  rcases family_descends (prefixWord ++ tailWord_6924378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6924436 : List Nat := [2, 4, 2, 3, 1, 2, 1, 3, 5]
def baseStart_6924436 : Nat := 118140960795 + 6924436 * 2 ^ 59
def prefixEnd_6924436 : Nat := 4983230072969 + 3 ^ 40 * 6924436 * 2
def baseEnd_6924436 : Nat := 395062658810708371778345

theorem tailTrace_6924436 : CollatzResearch.WordTrace tailWord_6924436 prefixEnd_6924436 395062658810708371778345 := by
  unfold tailWord_6924436
  simp only [CollatzResearch.WordTrace]
  refine ⟨126277464570979223181176581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168369952761305630908235441 126277464570979223181176581)
  ·
    refine ⟨23677024607058604346470609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126277464570979223181176581 23677024607058604346470609)
    ·
      refine ⟨17757768455293953259852957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23677024607058604346470609 17757768455293953259852957)
      ·
        refine ⟨6659163170735232472444859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17757768455293953259852957 6659163170735232472444859)
        ·
          refine ⟨9988744756102848708667289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6659163170735232472444859 9988744756102848708667289)
          ·
            refine ⟨7491558567077136531500467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9988744756102848708667289 7491558567077136531500467)
            ·
              refine ⟨11237337850615704797250701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7491558567077136531500467 11237337850615704797250701)
              ·
                refine ⟨4214001693980889298969013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11237337850615704797250701 4214001693980889298969013)
                ·
                  refine ⟨395062658810708371778345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4214001693980889298969013 395062658810708371778345)
                  ·
                    rfl

theorem cell23_6924436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 3, 5].length) (baseStart_6924436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6924436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6924436 prefixEnd_6924436 := by exact prefixLift 6924436
  have htrace : WordTrace (prefixWord ++ tailWord_6924436) baseStart_6924436 baseEnd_6924436 := by
    simpa [prefixWord, tailWord_6924436, baseEnd_6924436] using wordTrace_append hprefix tailTrace_6924436
  have hstable : (prefixWord ++ tailWord_6924436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6924436).length < 2 ^ (prefixWord ++ tailWord_6924436).sum := by decide
  have hdescent : baseEnd_6924436 < baseStart_6924436 := by decide
  rcases family_descends (prefixWord ++ tailWord_6924436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6924452 : List Nat := [2, 3, 1, 2, 4, 1, 1, 2, 2, 1, 4]
def baseStart_6924452 : Nat := 118140960795 + 6924452 * 2 ^ 59
def prefixEnd_6924452 : Nat := 4983230072969 + 3 ^ 40 * 6924452 * 2
def baseEnd_6924452 : Nat := 3555572144986847283405031

theorem tailTrace_6924452 : CollatzResearch.WordTrace tailWord_6924452 prefixEnd_6924452 3555572144986847283405031 := by
  unfold tailWord_6924452
  simp only [CollatzResearch.WordTrace]
  refine ⟨126277756354950240547467805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168370341806600320729957073 126277756354950240547467805)
  ·
    refine ⟨47354158633106340205300427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126277756354950240547467805 47354158633106340205300427)
    ·
      refine ⟨71031237949659510307950641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47354158633106340205300427 71031237949659510307950641)
      ·
        refine ⟨53273428462244632730962981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71031237949659510307950641 53273428462244632730962981)
        ·
          refine ⟨9988767836670868637055559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53273428462244632730962981 9988767836670868637055559)
          ·
            refine ⟨14983151755006302955583339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9988767836670868637055559 14983151755006302955583339)
            ·
              refine ⟨22474727632509454433375009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14983151755006302955583339 22474727632509454433375009)
              ·
                refine ⟨16856045724382090825031257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22474727632509454433375009 16856045724382090825031257)
                ·
                  refine ⟨12642034293286568118773443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16856045724382090825031257 12642034293286568118773443)
                  ·
                    refine ⟨18963051439929852178160165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12642034293286568118773443 18963051439929852178160165)
                    ·
                      refine ⟨3555572144986847283405031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18963051439929852178160165 3555572144986847283405031)
                      ·
                        rfl

theorem cell23_6924452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 2, 2, 1, 4].length) (baseStart_6924452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6924452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6924452 prefixEnd_6924452 := by exact prefixLift 6924452
  have htrace : WordTrace (prefixWord ++ tailWord_6924452) baseStart_6924452 baseEnd_6924452 := by
    simpa [prefixWord, tailWord_6924452, baseEnd_6924452] using wordTrace_append hprefix tailTrace_6924452
  have hstable : (prefixWord ++ tailWord_6924452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6924452).length < 2 ^ (prefixWord ++ tailWord_6924452).sum := by decide
  have hdescent : baseEnd_6924452 < baseStart_6924452 := by decide
  rcases family_descends (prefixWord ++ tailWord_6924452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6924505 : List Nat := [1, 2, 1, 2, 3, 1, 2, 5, 1, 5]
def baseStart_6924505 : Nat := 118140960795 + 6924505 * 2 ^ 59
def prefixEnd_6924505 : Nat := 4983230072969 + 3 ^ 40 * 6924505 * 2
def baseEnd_6924505 : Nat := 1185199786487178525347429

theorem tailTrace_6924505 : CollatzResearch.WordTrace tailWord_6924505 prefixEnd_6924505 1185199786487178525347429 := by
  unfold tailWord_6924505
  simp only [CollatzResearch.WordTrace]
  refine ⟨252557445778708471146614969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168371630519138980764409979 252557445778708471146614969)
  ·
    refine ⟨189418084334031353359961227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252557445778708471146614969 189418084334031353359961227)
    ·
      refine ⟨284127126501047030039941841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189418084334031353359961227 284127126501047030039941841)
      ·
        refine ⟨213095344875785272529956381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 284127126501047030039941841 213095344875785272529956381)
        ·
          refine ⟨79910754328419477198733643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 213095344875785272529956381 79910754328419477198733643)
          ·
            refine ⟨119866131492629215798100465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79910754328419477198733643 119866131492629215798100465)
            ·
              refine ⟨89899598619471911848575349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119866131492629215798100465 89899598619471911848575349)
              ·
                refine ⟨8428087370575491735803939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89899598619471911848575349 8428087370575491735803939)
                ·
                  refine ⟨12642131055863237603705909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8428087370575491735803939 12642131055863237603705909)
                  ·
                    refine ⟨1185199786487178525347429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12642131055863237603705909 1185199786487178525347429)
                    ·
                      rfl

theorem cell23_6924505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 5, 1, 5].length) (baseStart_6924505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6924505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6924505 prefixEnd_6924505 := by exact prefixLift 6924505
  have htrace : WordTrace (prefixWord ++ tailWord_6924505) baseStart_6924505 baseEnd_6924505 := by
    simpa [prefixWord, tailWord_6924505, baseEnd_6924505] using wordTrace_append hprefix tailTrace_6924505
  have hstable : (prefixWord ++ tailWord_6924505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6924505).length < 2 ^ (prefixWord ++ tailWord_6924505).sum := by decide
  have hdescent : baseEnd_6924505 < baseStart_6924505 := by decide
  rcases family_descends (prefixWord ++ tailWord_6924505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6924512 : List Nat := [2, 1, 1, 3, 1, 3, 1, 4, 2, 3, 2]
def baseStart_6924512 : Nat := 118140960795 + 6924512 * 2 ^ 59
def prefixEnd_6924512 : Nat := 4983230072969 + 3 ^ 40 * 6924512 * 2
def baseEnd_6924512 : Nat := 3555602953826117048654755

theorem tailTrace_6924512 : CollatzResearch.WordTrace tailWord_6924512 prefixEnd_6924512 3555602953826117048654755 := by
  unfold tailWord_6924512
  simp only [CollatzResearch.WordTrace]
  refine ⟨126278850544841555671059895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168371800726455407561413193 126278850544841555671059895)
  ·
    refine ⟨189418275817262333506589843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126278850544841555671059895 189418275817262333506589843)
    ·
      refine ⟨284127413725893500259884765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189418275817262333506589843 284127413725893500259884765)
      ·
        refine ⟨106547780147210062597456787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 284127413725893500259884765 106547780147210062597456787)
        ·
          refine ⟨159821670220815093896185181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106547780147210062597456787 159821670220815093896185181)
          ·
            refine ⟨59933126332805660211069443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159821670220815093896185181 59933126332805660211069443)
            ·
              refine ⟨89899689499208490316604165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59933126332805660211069443 89899689499208490316604165)
              ·
                refine ⟨16856191781101591934363281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89899689499208490316604165 16856191781101591934363281)
                ·
                  refine ⟨12642143835826193950772461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16856191781101591934363281 12642143835826193950772461)
                  ·
                    refine ⟨4740803938434822731539673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12642143835826193950772461 4740803938434822731539673)
                    ·
                      refine ⟨3555602953826117048654755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4740803938434822731539673 3555602953826117048654755)
                      ·
                        rfl

theorem cell23_6924512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 4, 2, 3, 2].length) (baseStart_6924512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6924512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6924512 prefixEnd_6924512 := by exact prefixLift 6924512
  have htrace : WordTrace (prefixWord ++ tailWord_6924512) baseStart_6924512 baseEnd_6924512 := by
    simpa [prefixWord, tailWord_6924512, baseEnd_6924512] using wordTrace_append hprefix tailTrace_6924512
  have hstable : (prefixWord ++ tailWord_6924512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6924512).length < 2 ^ (prefixWord ++ tailWord_6924512).sum := by decide
  have hdescent : baseEnd_6924512 < baseStart_6924512 := by decide
  rcases family_descends (prefixWord ++ tailWord_6924512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6924542 : List Nat := [4, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4]
def baseStart_6924542 : Nat := 118140960795 + 6924542 * 2 ^ 59
def prefixEnd_6924542 : Nat := 4983230072969 + 3 ^ 40 * 6924542 * 2
def baseEnd_6924542 : Nat := 3555618358245751931279617

theorem tailTrace_6924542 : CollatzResearch.WordTrace tailWord_6924542 prefixEnd_6924542 3555618358245751931279617 := by
  unfold tailWord_6924542
  simp only [CollatzResearch.WordTrace]
  refine ⟨31569849409946803308213985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168372530186382950977141253 31569849409946803308213985)
  ·
    refine ⟨23677387057460102481160489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31569849409946803308213985 23677387057460102481160489)
    ·
      refine ⟨17758040293095076860870367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23677387057460102481160489 17758040293095076860870367)
      ·
        refine ⟨26637060439642615291305551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17758040293095076860870367 26637060439642615291305551)
        ·
          refine ⟨39955590659463922936958327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26637060439642615291305551 39955590659463922936958327)
          ·
            refine ⟨59933385989195884405437491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39955590659463922936958327 59933385989195884405437491)
            ·
              refine ⟨89900078983793826608156237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59933385989195884405437491 89900078983793826608156237)
              ·
                refine ⟨33712529618922684978058589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89900078983793826608156237 33712529618922684978058589)
                ·
                  refine ⟨12642198607096006866771971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33712529618922684978058589 12642198607096006866771971)
                  ·
                    refine ⟨18963297910644010300157957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12642198607096006866771971 18963297910644010300157957)
                    ·
                      refine ⟨3555618358245751931279617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18963297910644010300157957 3555618358245751931279617)
                      ·
                        rfl

theorem cell23_6924542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_6924542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6924542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6924542 prefixEnd_6924542 := by exact prefixLift 6924542
  have htrace : WordTrace (prefixWord ++ tailWord_6924542) baseStart_6924542 baseEnd_6924542 := by
    simpa [prefixWord, tailWord_6924542, baseEnd_6924542] using wordTrace_append hprefix tailTrace_6924542
  have hstable : (prefixWord ++ tailWord_6924542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6924542).length < 2 ^ (prefixWord ++ tailWord_6924542).sum := by decide
  have hdescent : baseEnd_6924542 < baseStart_6924542 := by decide
  rcases family_descends (prefixWord ++ tailWord_6924542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6924546 : List Nat := [3, 4, 1, 1, 2, 1, 3, 1, 2, 3, 2]
def baseStart_6924546 : Nat := 118140960795 + 6924546 * 2 ^ 59
def prefixEnd_6924546 : Nat := 4983230072969 + 3 ^ 40 * 6924546 * 2
def baseEnd_6924546 : Nat := 3555620412168369915629599

theorem tailTrace_6924546 : CollatzResearch.WordTrace tailWord_6924546 prefixEnd_6924546 3555620412168369915629599 := by
  unfold tailWord_6924546
  simp only [CollatzResearch.WordTrace]
  refine ⟨63139735292889983787214373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168372627447706623432571661 63139735292889983787214373)
  ·
    refine ⟨11838700367416871960102695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63139735292889983787214373 11838700367416871960102695)
    ·
      refine ⟨17758050551125307940154043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11838700367416871960102695 17758050551125307940154043)
      ·
        refine ⟨26637075826687961910231065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17758050551125307940154043 26637075826687961910231065)
        ·
          refine ⟨19977806870015971432673299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26637075826687961910231065 19977806870015971432673299)
          ·
            refine ⟨29966710305023957149009949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19977806870015971432673299 29966710305023957149009949)
            ·
              refine ⟨11237516364383983930878731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29966710305023957149009949 11237516364383983930878731)
              ·
                refine ⟨16856274546575975896318097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11237516364383983930878731 16856274546575975896318097)
                ·
                  refine ⟨12642205909931981922238573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16856274546575975896318097 12642205909931981922238573)
                  ·
                    refine ⟨4740827216224493220839465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12642205909931981922238573 4740827216224493220839465)
                    ·
                      refine ⟨3555620412168369915629599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4740827216224493220839465 3555620412168369915629599)
                      ·
                        rfl

theorem cell23_6924546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 1, 2, 3, 2].length) (baseStart_6924546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6924546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6924546 prefixEnd_6924546 := by exact prefixLift 6924546
  have htrace : WordTrace (prefixWord ++ tailWord_6924546) baseStart_6924546 baseEnd_6924546 := by
    simpa [prefixWord, tailWord_6924546, baseEnd_6924546] using wordTrace_append hprefix tailTrace_6924546
  have hstable : (prefixWord ++ tailWord_6924546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6924546).length < 2 ^ (prefixWord ++ tailWord_6924546).sum := by decide
  have hdescent : baseEnd_6924546 < baseStart_6924546 := by decide
  rcases family_descends (prefixWord ++ tailWord_6924546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6924555 : List Nat := [1, 1, 1, 1, 5, 2, 1, 4, 1, 2, 4]
def baseStart_6924555 : Nat := 118140960795 + 6924555 * 2 ^ 59
def prefixEnd_6924555 : Nat := 4983230072969 + 3 ^ 40 * 6924555 * 2
def baseEnd_6924555 : Nat := 3555625033494260380417057

theorem tailTrace_6924555 : CollatzResearch.WordTrace tailWord_6924555 prefixEnd_6924555 3555625033494260380417057 := by
  unfold tailWord_6924555
  simp only [CollatzResearch.WordTrace]
  refine ⟨252559269428527329685935119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168372846285684886457290079 252559269428527329685935119)
  ·
    refine ⟨378838904142790994528902679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252559269428527329685935119 378838904142790994528902679)
    ·
      refine ⟨568258356214186491793354019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378838904142790994528902679 568258356214186491793354019)
      ·
        refine ⟨852387534321279737690031029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 568258356214186491793354019 852387534321279737690031029)
        ·
          refine ⟨79911331342619975408440409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 852387534321279737690031029 79911331342619975408440409)
          ·
            refine ⟨59933498506964981556330307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79911331342619975408440409 59933498506964981556330307)
            ·
              refine ⟨89900247760447472334495461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59933498506964981556330307 89900247760447472334495461)
              ·
                refine ⟨16856296455083901062717899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89900247760447472334495461 16856296455083901062717899)
                ·
                  refine ⟨25284444682625851594076849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16856296455083901062717899 25284444682625851594076849)
                  ·
                    refine ⟨18963333511969388695557637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25284444682625851594076849 18963333511969388695557637)
                    ·
                      refine ⟨3555625033494260380417057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18963333511969388695557637 3555625033494260380417057)
                      ·
                        rfl

theorem cell23_6924555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 4, 1, 2, 4].length) (baseStart_6924555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6924555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6924555 prefixEnd_6924555 := by exact prefixLift 6924555
  have htrace : WordTrace (prefixWord ++ tailWord_6924555) baseStart_6924555 baseEnd_6924555 := by
    simpa [prefixWord, tailWord_6924555, baseEnd_6924555] using wordTrace_append hprefix tailTrace_6924555
  have hstable : (prefixWord ++ tailWord_6924555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6924555).length < 2 ^ (prefixWord ++ tailWord_6924555).sum := by decide
  have hdescent : baseEnd_6924555 < baseStart_6924555 := by decide
  rcases family_descends (prefixWord ++ tailWord_6924555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6924576 : List Nat := [2, 1, 1, 5, 2, 2, 2, 1, 3, 2, 2]
def baseStart_6924576 : Nat := 118140960795 + 6924576 * 2 ^ 59
def prefixEnd_6924576 : Nat := 4983230072969 + 3 ^ 40 * 6924576 * 2
def baseEnd_6924576 : Nat := 3555635816588004798254461

theorem tailTrace_6924576 : CollatzResearch.WordTrace tailWord_6924576 prefixEnd_6924576 3555635816588004798254461 := by
  unfold tailWord_6924576
  simp only [CollatzResearch.WordTrace]
  refine ⟨126280017680725625136224791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168373356907634166848299721 126280017680725625136224791)
  ·
    refine ⟨189420026521088437704337187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126280017680725625136224791 189420026521088437704337187)
    ·
      refine ⟨284130039781632656556505781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189420026521088437704337187 284130039781632656556505781)
      ·
        refine ⟨26637191229528061552172417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 284130039781632656556505781 26637191229528061552172417)
        ·
          refine ⟨19977893422146046164129313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26637191229528061552172417 19977893422146046164129313)
          ·
            refine ⟨14983420066609534623096985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19977893422146046164129313 14983420066609534623096985)
            ·
              refine ⟨11237565049957150967322739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14983420066609534623096985 11237565049957150967322739)
              ·
                refine ⟨16856347574935726450984109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11237565049957150967322739 16856347574935726450984109)
                ·
                  refine ⟨6321130340600897419119041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16856347574935726450984109 6321130340600897419119041)
                  ·
                    refine ⟨4740847755450673064339281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6321130340600897419119041 4740847755450673064339281)
                    ·
                      refine ⟨3555635816588004798254461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4740847755450673064339281 3555635816588004798254461)
                      ·
                        rfl

theorem cell23_6924576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 1, 3, 2, 2].length) (baseStart_6924576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6924576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6924576 prefixEnd_6924576 := by exact prefixLift 6924576
  have htrace : WordTrace (prefixWord ++ tailWord_6924576) baseStart_6924576 baseEnd_6924576 := by
    simpa [prefixWord, tailWord_6924576, baseEnd_6924576] using wordTrace_append hprefix tailTrace_6924576
  have hstable : (prefixWord ++ tailWord_6924576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6924576).length < 2 ^ (prefixWord ++ tailWord_6924576).sum := by decide
  have hdescent : baseEnd_6924576 < baseStart_6924576 := by decide
  rcases family_descends (prefixWord ++ tailWord_6924576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6924586 : List Nat := [3, 1, 4, 2, 3, 1, 1, 1, 1, 6]
def baseStart_6924586 : Nat := 118140960795 + 6924586 * 2 ^ 59
def prefixEnd_6924586 : Nat := 4983230072969 + 3 ^ 40 * 6924586 * 2
def baseEnd_6924586 : Nat := 1185213650464849919709805

theorem tailTrace_6924586 : CollatzResearch.WordTrace tailWord_6924586 prefixEnd_6924586 1185213650464849919709805 := by
  unfold tailWord_6924586
  simp only [CollatzResearch.WordTrace]
  refine ⟨63140100022853755495078403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168373600060943347986875741 63140100022853755495078403)
  ·
    refine ⟨94710150034280633242617605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63140100022853755495078403 94710150034280633242617605)
    ·
      refine ⟨17758153131427618732990801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94710150034280633242617605 17758153131427618732990801)
      ·
        refine ⟨13318614848570714049743101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17758153131427618732990801 13318614848570714049743101)
        ·
          refine ⟨4994480568214017768653663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13318614848570714049743101 4994480568214017768653663)
          ·
            refine ⟨7491720852321026652980495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4994480568214017768653663 7491720852321026652980495)
            ·
              refine ⟨11237581278481539979470743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7491720852321026652980495 11237581278481539979470743)
              ·
                refine ⟨16856371917722309969206115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11237581278481539979470743 16856371917722309969206115)
                ·
                  refine ⟨25284557876583464953809173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16856371917722309969206115 25284557876583464953809173)
                  ·
                    refine ⟨1185213650464849919709805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25284557876583464953809173 1185213650464849919709805)
                    ·
                      rfl

theorem cell23_6924586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_6924586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6924586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6924586 prefixEnd_6924586 := by exact prefixLift 6924586
  have htrace : WordTrace (prefixWord ++ tailWord_6924586) baseStart_6924586 baseEnd_6924586 := by
    simpa [prefixWord, tailWord_6924586, baseEnd_6924586] using wordTrace_append hprefix tailTrace_6924586
  have hstable : (prefixWord ++ tailWord_6924586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6924586).length < 2 ^ (prefixWord ++ tailWord_6924586).sum := by decide
  have hdescent : baseEnd_6924586 < baseStart_6924586 := by decide
  rcases family_descends (prefixWord ++ tailWord_6924586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6924589 : List Nat := [1, 5, 3, 1, 2, 1, 1, 1, 1, 1, 6]
def baseStart_6924589 : Nat := 118140960795 + 6924589 * 2 ^ 59
def prefixEnd_6924589 : Nat := 4983230072969 + 3 ^ 40 * 6924589 * 2
def baseEnd_6924589 : Nat := 3555642491836513247391901

theorem tailTrace_6924589 : CollatzResearch.WordTrace tailWord_6924589 prefixEnd_6924589 3555642491836513247391901 := by
  unfold tailWord_6924589
  simp only [CollatzResearch.WordTrace]
  refine ⟨252560509510404153492672821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168373673006936102328448547 252560509510404153492672821)
  ·
    refine ⟨23677547766600389389938077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 252560509510404153492672821 23677547766600389389938077)
    ·
      refine ⟨8879080412475146021226779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23677547766600389389938077 8879080412475146021226779)
      ·
        refine ⟨13318620618712719031840169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8879080412475146021226779 13318620618712719031840169)
        ·
          refine ⟨9988965464034539273880127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13318620618712719031840169 9988965464034539273880127)
          ·
            refine ⟨14983448196051808910820191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9988965464034539273880127 14983448196051808910820191)
            ·
              refine ⟨22475172294077713366230287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14983448196051808910820191 22475172294077713366230287)
              ·
                refine ⟨33712758441116570049345431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22475172294077713366230287 33712758441116570049345431)
                ·
                  refine ⟨50569137661674855074018147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33712758441116570049345431 50569137661674855074018147)
                  ·
                    refine ⟨75853706492512282611027221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50569137661674855074018147 75853706492512282611027221)
                    ·
                      refine ⟨3555642491836513247391901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75853706492512282611027221 3555642491836513247391901)
                      ·
                        rfl

theorem cell23_6924589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_6924589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6924589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6924589 prefixEnd_6924589 := by exact prefixLift 6924589
  have htrace : WordTrace (prefixWord ++ tailWord_6924589) baseStart_6924589 baseEnd_6924589 := by
    simpa [prefixWord, tailWord_6924589, baseEnd_6924589] using wordTrace_append hprefix tailTrace_6924589
  have hstable : (prefixWord ++ tailWord_6924589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6924589).length < 2 ^ (prefixWord ++ tailWord_6924589).sum := by decide
  have hdescent : baseEnd_6924589 < baseStart_6924589 := by decide
  rcases family_descends (prefixWord ++ tailWord_6924589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6924596 : List Nat := [2, 5, 1, 1, 1, 3, 2, 2, 1, 2, 3]
def baseStart_6924596 : Nat := 118140960795 + 6924596 * 2 ^ 59
def prefixEnd_6924596 : Nat := 4983230072969 + 3 ^ 40 * 6924596 * 2
def baseEnd_6924596 : Nat := 3555646086201094720004369

theorem tailTrace_6924596 : CollatzResearch.WordTrace tailWord_6924596 prefixEnd_6924596 3555646086201094720004369 := by
  unfold tailWord_6924596
  simp only [CollatzResearch.WordTrace]
  refine ⟨126280382410689396844088821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168373843214252529125451761 126280382410689396844088821)
  ·
    refine ⟨11838785851002130954133327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 126280382410689396844088821 11838785851002130954133327)
    ·
      refine ⟨17758178776503196431199991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11838785851002130954133327 17758178776503196431199991)
      ·
        refine ⟨26637268164754794646799987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17758178776503196431199991 26637268164754794646799987)
        ·
          refine ⟨39955902247132191970199981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26637268164754794646799987 39955902247132191970199981)
          ·
            refine ⟨14983463342674571988824993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39955902247132191970199981 14983463342674571988824993)
            ·
              refine ⟨11237597507005928991618745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14983463342674571988824993 11237597507005928991618745)
              ·
                refine ⟨8428198130254446743714059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11237597507005928991618745 8428198130254446743714059)
                ·
                  refine ⟨12642297195381670115571089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8428198130254446743714059 12642297195381670115571089)
                  ·
                    refine ⟨9481722896536252586678317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12642297195381670115571089 9481722896536252586678317)
                    ·
                      refine ⟨3555646086201094720004369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9481722896536252586678317 3555646086201094720004369)
                      ·
                        rfl

theorem cell23_6924596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_6924596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6924596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6924596 prefixEnd_6924596 := by exact prefixLift 6924596
  have htrace : WordTrace (prefixWord ++ tailWord_6924596) baseStart_6924596 baseEnd_6924596 := by
    simpa [prefixWord, tailWord_6924596, baseEnd_6924596] using wordTrace_append hprefix tailTrace_6924596
  have hstable : (prefixWord ++ tailWord_6924596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6924596).length < 2 ^ (prefixWord ++ tailWord_6924596).sum := by decide
  have hdescent : baseEnd_6924596 < baseStart_6924596 := by decide
  rcases family_descends (prefixWord ++ tailWord_6924596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6924632 : List Nat := [2, 1, 2, 2, 1, 1, 2, 1, 5, 4, 2]
def baseStart_6924632 : Nat := 118140960795 + 6924632 * 2 ^ 59
def prefixEnd_6924632 : Nat := 4983230072969 + 3 ^ 40 * 6924632 * 2
def baseEnd_6924632 : Nat := 3555664571504656579154203

theorem tailTrace_6924632 : CollatzResearch.WordTrace tailWord_6924632 prefixEnd_6924632 3555664571504656579154203 := by
  unfold tailWord_6924632
  simp only [CollatzResearch.WordTrace]
  refine ⟨126281038924624185918244075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168374718566165581224325433 126281038924624185918244075)
  ·
    refine ⟨189421558386936278877366113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126281038924624185918244075 189421558386936278877366113)
    ·
      refine ⟨142066168790202209158024585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189421558386936278877366113 142066168790202209158024585)
      ·
        refine ⟨106549626592651656868518439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142066168790202209158024585 106549626592651656868518439)
        ·
          refine ⟨159824439888977485302777659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106549626592651656868518439 159824439888977485302777659)
          ·
            refine ⟨239736659833466227954166489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159824439888977485302777659 239736659833466227954166489)
            ·
              refine ⟨179802494875099670965624867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 239736659833466227954166489 179802494875099670965624867)
              ·
                refine ⟨269703742312649506448437301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179802494875099670965624867 269703742312649506448437301)
                ·
                  refine ⟨25284725841810891229540997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 269703742312649506448437301 25284725841810891229540997)
                  ·
                    refine ⟨4740886095339542105538937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25284725841810891229540997 4740886095339542105538937)
                    ·
                      refine ⟨3555664571504656579154203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4740886095339542105538937 3555664571504656579154203)
                      ·
                        rfl

theorem cell23_6924632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 5, 4, 2].length) (baseStart_6924632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6924632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6924632 prefixEnd_6924632 := by exact prefixLift 6924632
  have htrace : WordTrace (prefixWord ++ tailWord_6924632) baseStart_6924632 baseEnd_6924632 := by
    simpa [prefixWord, tailWord_6924632, baseEnd_6924632] using wordTrace_append hprefix tailTrace_6924632
  have hstable : (prefixWord ++ tailWord_6924632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6924632).length < 2 ^ (prefixWord ++ tailWord_6924632).sum := by decide
  have hdescent : baseEnd_6924632 < baseStart_6924632 := by decide
  rcases family_descends (prefixWord ++ tailWord_6924632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6924722 : List Nat := [3, 2, 1, 1, 1, 1, 5, 1, 1, 3, 4]
def baseStart_6924722 : Nat := 118140960795 + 6924722 * 2 ^ 59
def prefixEnd_6924722 : Nat := 4983230072969 + 3 ^ 40 * 6924722 * 2
def baseEnd_6924722 : Nat := 3555710784763561227028789

theorem tailTrace_6924722 : CollatzResearch.WordTrace tailWord_6924722 prefixEnd_6924722 3555710784763561227028789 := by
  unfold tailWord_6924722
  simp only [CollatzResearch.WordTrace]
  refine ⟨63141340104730579301816105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168376906945948211471509613 63141340104730579301816105)
  ·
    refine ⟨47356005078547934476362079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63141340104730579301816105 47356005078547934476362079)
    ·
      refine ⟨71034007617821901714543119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47356005078547934476362079 71034007617821901714543119)
      ·
        refine ⟨106551011426732852571814679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71034007617821901714543119 106551011426732852571814679)
        ·
          refine ⟨159826517140099278857722019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106551011426732852571814679 159826517140099278857722019)
          ·
            refine ⟨239739775710148918286583029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159826517140099278857722019 239739775710148918286583029)
            ·
              refine ⟨22475603972826461089367159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 239739775710148918286583029 22475603972826461089367159)
              ·
                refine ⟨33713405959239691634050739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22475603972826461089367159 33713405959239691634050739)
                ·
                  refine ⟨50570108938859537451076109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33713405959239691634050739 50570108938859537451076109)
                  ·
                    refine ⟨18963790852072326544153541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50570108938859537451076109 18963790852072326544153541)
                    ·
                      refine ⟨3555710784763561227028789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18963790852072326544153541 3555710784763561227028789)
                      ·
                        rfl

theorem cell23_6924722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 1, 3, 4].length) (baseStart_6924722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6924722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6924722 prefixEnd_6924722 := by exact prefixLift 6924722
  have htrace : WordTrace (prefixWord ++ tailWord_6924722) baseStart_6924722 baseEnd_6924722 := by
    simpa [prefixWord, tailWord_6924722, baseEnd_6924722] using wordTrace_append hprefix tailTrace_6924722
  have hstable : (prefixWord ++ tailWord_6924722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6924722).length < 2 ^ (prefixWord ++ tailWord_6924722).sum := by decide
  have hdescent : baseEnd_6924722 < baseStart_6924722 := by decide
  rcases family_descends (prefixWord ++ tailWord_6924722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6924755 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 9]
def baseStart_6924755 : Nat := 118140960795 + 6924755 * 2 ^ 59
def prefixEnd_6924755 : Nat := 4983230072969 + 3 ^ 40 * 6924755 * 2
def baseEnd_6924755 : Nat := 3555727729625159597916137

theorem tailTrace_6924755 : CollatzResearch.WordTrace tailWord_6924755 prefixEnd_6924755 3555727729625159597916137 := by
  unfold tailWord_6924755
  simp only [CollatzResearch.WordTrace]
  refine ⟨252566564027802763843215719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168377709351868509228810479 252566564027802763843215719)
  ·
    refine ⟨378849846041704145764823579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252566564027802763843215719 378849846041704145764823579)
    ·
      refine ⟨568274769062556218647235369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378849846041704145764823579 568274769062556218647235369)
      ·
        refine ⟨426206076796917163985426527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 568274769062556218647235369 426206076796917163985426527)
        ·
          refine ⟨639309115195375745978139791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426206076796917163985426527 639309115195375745978139791)
          ·
            refine ⟨958963672793063618967209687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 639309115195375745978139791 958963672793063618967209687)
            ·
              refine ⟨1438445509189595428450814531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 958963672793063618967209687 1438445509189595428450814531)
              ·
                refine ⟨2157668263784393142676221797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1438445509189595428450814531 2157668263784393142676221797)
                ·
                  refine ⟨404562799459573714251791587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2157668263784393142676221797 404562799459573714251791587)
                  ·
                    refine ⟨606844199189360571377687381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 404562799459573714251791587 606844199189360571377687381)
                    ·
                      refine ⟨3555727729625159597916137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 606844199189360571377687381 3555727729625159597916137)
                      ·
                        rfl

theorem cell23_6924755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 9].length) (baseStart_6924755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6924755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6924755 prefixEnd_6924755 := by exact prefixLift 6924755
  have htrace : WordTrace (prefixWord ++ tailWord_6924755) baseStart_6924755 baseEnd_6924755 := by
    simpa [prefixWord, tailWord_6924755, baseEnd_6924755] using wordTrace_append hprefix tailTrace_6924755
  have hstable : (prefixWord ++ tailWord_6924755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6924755).length < 2 ^ (prefixWord ++ tailWord_6924755).sum := by decide
  have hdescent : baseEnd_6924755 < baseStart_6924755 := by decide
  rcases family_descends (prefixWord ++ tailWord_6924755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6924756 : List Nat := [2, 4, 1, 2, 2, 1, 2, 1, 2, 4, 2]
def baseStart_6924756 : Nat := 118140960795 + 6924756 * 2 ^ 59
def prefixEnd_6924756 : Nat := 4983230072969 + 3 ^ 40 * 6924756 * 2
def baseEnd_6924756 : Nat := 3555728243105814094003633

theorem tailTrace_6924756 : CollatzResearch.WordTrace tailWord_6924756 prefixEnd_6924756 3555728243105814094003633 := by
  unfold tailWord_6924756
  simp only [CollatzResearch.WordTrace]
  refine ⟨126283300250399570507001061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168377733667199427342668081 126283300250399570507001061)
  ·
    refine ⟨23678118796949919470062699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126283300250399570507001061 23678118796949919470062699)
    ·
      refine ⟨35517178195424879205094049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23678118796949919470062699 35517178195424879205094049)
      ·
        refine ⟨26637883646568659403820537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35517178195424879205094049 26637883646568659403820537)
        ·
          refine ⟨19978412734926494552865403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26637883646568659403820537 19978412734926494552865403)
          ·
            refine ⟨29967619102389741829298105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19978412734926494552865403 29967619102389741829298105)
            ·
              refine ⟨22475714326792306371973579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29967619102389741829298105 22475714326792306371973579)
              ·
                refine ⟨33713571490188459557960369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22475714326792306371973579 33713571490188459557960369)
                ·
                  refine ⟨25285178617641344668470277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33713571490188459557960369 25285178617641344668470277)
                  ·
                    refine ⟨4740970990807752125338177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25285178617641344668470277 4740970990807752125338177)
                    ·
                      refine ⟨3555728243105814094003633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4740970990807752125338177 3555728243105814094003633)
                      ·
                        rfl

theorem cell23_6924756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 2, 4, 2].length) (baseStart_6924756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6924756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6924756 prefixEnd_6924756 := by exact prefixLift 6924756
  have htrace : WordTrace (prefixWord ++ tailWord_6924756) baseStart_6924756 baseEnd_6924756 := by
    simpa [prefixWord, tailWord_6924756, baseEnd_6924756] using wordTrace_append hprefix tailTrace_6924756
  have hstable : (prefixWord ++ tailWord_6924756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6924756).length < 2 ^ (prefixWord ++ tailWord_6924756).sum := by decide
  have hdescent : baseEnd_6924756 < baseStart_6924756 := by decide
  rcases family_descends (prefixWord ++ tailWord_6924756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6924813 : List Nat := [1, 7, 1, 1, 1, 2, 1, 3, 6]
def baseStart_6924813 : Nat := 118140960795 + 6924813 * 2 ^ 59
def prefixEnd_6924813 : Nat := 4983230072969 + 3 ^ 40 * 6924813 * 2
def baseEnd_6924813 : Nat := 395084167944791152332319

theorem tailTrace_6924813 : CollatzResearch.WordTrace tailWord_6924813 prefixEnd_6924813 395084167944791152332319 := by
  unfold tailWord_6924813
  simp only [CollatzResearch.WordTrace]
  refine ⟨252568679461592639748827093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168379119641061759832551395 252568679461592639748827093)
  ·
    refine ⟨5919578424881077494113135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 252568679461592639748827093 5919578424881077494113135)
    ·
      refine ⟨8879367637321616241169703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5919578424881077494113135 8879367637321616241169703)
      ·
        refine ⟨13319051455982424361754555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8879367637321616241169703 13319051455982424361754555)
        ·
          refine ⟨19978577183973636542631833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13319051455982424361754555 19978577183973636542631833)
          ·
            refine ⟨14983932887980227406973875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19978577183973636542631833 14983932887980227406973875)
            ·
              refine ⟨22475899331970341110460813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14983932887980227406973875 22475899331970341110460813)
              ·
                refine ⟨8428462249488877916422805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22475899331970341110460813 8428462249488877916422805)
                ·
                  refine ⟨395084167944791152332319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8428462249488877916422805 395084167944791152332319)
                  ·
                    rfl

theorem cell23_6924813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_6924813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6924813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6924813 prefixEnd_6924813 := by exact prefixLift 6924813
  have htrace : WordTrace (prefixWord ++ tailWord_6924813) baseStart_6924813 baseEnd_6924813 := by
    simpa [prefixWord, tailWord_6924813, baseEnd_6924813] using wordTrace_append hprefix tailTrace_6924813
  have hstable : (prefixWord ++ tailWord_6924813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6924813).length < 2 ^ (prefixWord ++ tailWord_6924813).sum := by decide
  have hdescent : baseEnd_6924813 < baseStart_6924813 := by decide
  rcases family_descends (prefixWord ++ tailWord_6924813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6924849 : List Nat := [1, 2, 2, 3, 1, 1, 5, 1, 1, 1, 5]
def baseStart_6924849 : Nat := 118140960795 + 6924849 * 2 ^ 59
def prefixEnd_6924849 : Nat := 4983230072969 + 3 ^ 40 * 6924849 * 2
def baseEnd_6924849 : Nat := 3555775996806682230140705

theorem tailTrace_6924849 : CollatzResearch.WordTrace tailWord_6924849 prefixEnd_6924849 3555775996806682230140705 := by
  unfold tailWord_6924849
  simp only [CollatzResearch.WordTrace]
  refine ⟨252569992489462217897137601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168379994992974811931425067 252569992489462217897137601)
  ·
    refine ⟨189427494367096663422853201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252569992489462217897137601 189427494367096663422853201)
    ·
      refine ⟨142070620775322497567139901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189427494367096663422853201 142070620775322497567139901)
      ·
        refine ⟨53276482790745936587677463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142070620775322497567139901 53276482790745936587677463)
        ·
          refine ⟨79914724186118904881516195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53276482790745936587677463 79914724186118904881516195)
          ·
            refine ⟨119872086279178357322274293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79914724186118904881516195 119872086279178357322274293)
            ·
              refine ⟨11238008088672970998963215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 119872086279178357322274293 11238008088672970998963215)
              ·
                refine ⟨16857012133009456498444823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11238008088672970998963215 16857012133009456498444823)
                ·
                  refine ⟨25285518199514184747667235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16857012133009456498444823 25285518199514184747667235)
                  ·
                    refine ⟨37928277299271277121500853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25285518199514184747667235 37928277299271277121500853)
                    ·
                      refine ⟨3555775996806682230140705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37928277299271277121500853 3555775996806682230140705)
                      ·
                        rfl

theorem cell23_6924849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 1, 1, 1, 5].length) (baseStart_6924849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6924849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6924849 prefixEnd_6924849 := by exact prefixLift 6924849
  have htrace : WordTrace (prefixWord ++ tailWord_6924849) baseStart_6924849 baseEnd_6924849 := by
    simpa [prefixWord, tailWord_6924849, baseEnd_6924849] using wordTrace_append hprefix tailTrace_6924849
  have hstable : (prefixWord ++ tailWord_6924849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6924849).length < 2 ^ (prefixWord ++ tailWord_6924849).sum := by decide
  have hdescent : baseEnd_6924849 < baseStart_6924849 := by decide
  rcases family_descends (prefixWord ++ tailWord_6924849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6924856 : List Nat := [2, 1, 2, 1, 4, 1, 4, 2, 2, 4]
def baseStart_6924856 : Nat := 118140960795 + 6924856 * 2 ^ 59
def prefixEnd_6924856 : Nat := 4983230072969 + 3 ^ 40 * 6924856 * 2
def baseEnd_6924856 : Nat := 1185259863723754567584391

theorem tailTrace_6924856 : CollatzResearch.WordTrace tailWord_6924856 prefixEnd_6924856 1185259863723754567584391 := by
  unfold tailWord_6924856
  simp only [CollatzResearch.WordTrace]
  refine ⟨126285123900218429046321211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168380165200291238728428281 126285123900218429046321211)
  ·
    refine ⟨189427685850327643569481817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126285123900218429046321211 189427685850327643569481817)
    ·
      refine ⟨142070764387745732677111363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189427685850327643569481817 142070764387745732677111363)
      ·
        refine ⟨213106146581618599015667045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142070764387745732677111363 213106146581618599015667045)
        ·
          refine ⟨39957402484053487315437571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 213106146581618599015667045 39957402484053487315437571)
          ·
            refine ⟨59936103726080230973156357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39957402484053487315437571 59936103726080230973156357)
            ·
              refine ⟨11238019448640043307466817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59936103726080230973156357 11238019448640043307466817)
              ·
                refine ⟨8428514586480032480600113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11238019448640043307466817 8428514586480032480600113)
                ·
                  refine ⟨6321385939860024360450085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8428514586480032480600113 6321385939860024360450085)
                  ·
                    refine ⟨1185259863723754567584391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6321385939860024360450085 1185259863723754567584391)
                    ·
                      rfl

theorem cell23_6924856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 2, 2, 4].length) (baseStart_6924856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6924856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6924856 prefixEnd_6924856 := by exact prefixLift 6924856
  have htrace : WordTrace (prefixWord ++ tailWord_6924856) baseStart_6924856 baseEnd_6924856 := by
    simpa [prefixWord, tailWord_6924856, baseEnd_6924856] using wordTrace_append hprefix tailTrace_6924856
  have hstable : (prefixWord ++ tailWord_6924856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6924856).length < 2 ^ (prefixWord ++ tailWord_6924856).sum := by decide
  have hdescent : baseEnd_6924856 < baseStart_6924856 := by decide
  rcases family_descends (prefixWord ++ tailWord_6924856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6924869 : List Nat := [1, 3, 1, 1, 1, 7, 1, 8]
def baseStart_6924869 : Nat := 118140960795 + 6924869 * 2 ^ 59
def prefixEnd_6924869 : Nat := 4983230072969 + 3 ^ 40 * 6924869 * 2
def baseEnd_6924869 : Nat := 131695787645176746366319

theorem tailTrace_6924869 : CollatzResearch.WordTrace tailWord_6924869 prefixEnd_6924869 131695787645176746366319 := by
  unfold tailWord_6924869
  simp only [CollatzResearch.WordTrace]
  refine ⟨252570721949389761312865661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168380481299593174208577107 252570721949389761312865661)
  ·
    refine ⟨94714020731021160492324623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252570721949389761312865661 94714020731021160492324623)
    ·
      refine ⟨142071031096531740738486935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94714020731021160492324623 142071031096531740738486935)
      ·
        refine ⟨213106546644797611107730403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142071031096531740738486935 213106546644797611107730403)
        ·
          refine ⟨319659819967196416661595605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213106546644797611107730403 319659819967196416661595605)
          ·
            refine ⟨7492027030481166015506147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 319659819967196416661595605 7492027030481166015506147)
            ·
              refine ⟨11238040545721749023259221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7492027030481166015506147 11238040545721749023259221)
              ·
                refine ⟨131695787645176746366319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11238040545721749023259221 131695787645176746366319)
                ·
                  rfl

theorem cell23_6924869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 8].length) (baseStart_6924869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6924869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6924869 prefixEnd_6924869 := by exact prefixLift 6924869
  have htrace : WordTrace (prefixWord ++ tailWord_6924869) baseStart_6924869 baseEnd_6924869 := by
    simpa [prefixWord, tailWord_6924869, baseEnd_6924869] using wordTrace_append hprefix tailTrace_6924869
  have hstable : (prefixWord ++ tailWord_6924869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6924869).length < 2 ^ (prefixWord ++ tailWord_6924869).sum := by decide
  have hdescent : baseEnd_6924869 < baseStart_6924869 := by decide
  rcases family_descends (prefixWord ++ tailWord_6924869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6924872 : List Nat := [2, 1, 3, 1, 1, 1, 1, 3, 2, 2, 6]
def baseStart_6924872 : Nat := 118140960795 + 6924872 * 2 ^ 59
def prefixEnd_6924872 : Nat := 4983230072969 + 3 ^ 40 * 6924872 * 2
def baseEnd_6924872 : Nat := 3555787806861735640153099

theorem tailTrace_6924872 : CollatzResearch.WordTrace tailWord_6924872 prefixEnd_6924872 3555787806861735640153099 := by
  unfold tailWord_6924872
  simp only [CollatzResearch.WordTrace]
  refine ⟨126285415684189446412612435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168380554245585928550149913 126285415684189446412612435)
  ·
    refine ⟨189428123526284169618918653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126285415684189446412612435 189428123526284169618918653)
    ·
      refine ⟨71035546322356563607094495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189428123526284169618918653 71035546322356563607094495)
      ·
        refine ⟨106553319483534845410641743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71035546322356563607094495 106553319483534845410641743)
        ·
          refine ⟨159829979225302268115962615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106553319483534845410641743 159829979225302268115962615)
          ·
            refine ⟨239744968837953402173943923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159829979225302268115962615 239744968837953402173943923)
            ·
              refine ⟨359617453256930103260915885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239744968837953402173943923 359617453256930103260915885)
              ·
                refine ⟨134856544971348788722843457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 359617453256930103260915885 134856544971348788722843457)
                ·
                  refine ⟨101142408728511591542132593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134856544971348788722843457 101142408728511591542132593)
                  ·
                    refine ⟨75856806546383693656599445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 101142408728511591542132593 75856806546383693656599445)
                    ·
                      refine ⟨3555787806861735640153099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75856806546383693656599445 3555787806861735640153099)
                      ·
                        rfl

theorem cell23_6924872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_6924872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6924872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6924872 prefixEnd_6924872 := by exact prefixLift 6924872
  have htrace : WordTrace (prefixWord ++ tailWord_6924872) baseStart_6924872 baseEnd_6924872 := by
    simpa [prefixWord, tailWord_6924872, baseEnd_6924872] using wordTrace_append hprefix tailTrace_6924872
  have hstable : (prefixWord ++ tailWord_6924872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6924872).length < 2 ^ (prefixWord ++ tailWord_6924872).sum := by decide
  have hdescent : baseEnd_6924872 < baseStart_6924872 := by decide
  rcases family_descends (prefixWord ++ tailWord_6924872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6924879 : List Nat := [1, 1, 2, 1, 1, 2, 5, 3, 1, 3, 3]
def baseStart_6924879 : Nat := 118140960795 + 6924879 * 2 ^ 59
def prefixEnd_6924879 : Nat := 4983230072969 + 3 ^ 40 * 6924879 * 2
def baseEnd_6924879 : Nat := 3555791401226317112765567

theorem tailTrace_6924879 : CollatzResearch.WordTrace tailWord_6924879 prefixEnd_6924879 3555791401226317112765567 := by
  unfold tailWord_6924879
  simp only [CollatzResearch.WordTrace]
  refine ⟨252571086679353533020729691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168380724452902355347153127 252571086679353533020729691)
  ·
    refine ⟨378856630019030299531094537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252571086679353533020729691 378856630019030299531094537)
    ·
      refine ⟨284142472514272724648320903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 378856630019030299531094537 284142472514272724648320903)
      ·
        refine ⟨426213708771409086972481355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284142472514272724648320903 426213708771409086972481355)
        ·
          refine ⟨639320563157113630458722033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426213708771409086972481355 639320563157113630458722033)
          ·
            refine ⟨479490422367835222844041525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 639320563157113630458722033 479490422367835222844041525)
            ·
              refine ⟨44952227096984552141628893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 479490422367835222844041525 44952227096984552141628893)
              ·
                refine ⟨16857085161369207053110835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44952227096984552141628893 16857085161369207053110835)
                ·
                  refine ⟨25285627742053810579666253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16857085161369207053110835 25285627742053810579666253)
                  ·
                    refine ⟨9482110403270178967374845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25285627742053810579666253 9482110403270178967374845)
                    ·
                      refine ⟨3555791401226317112765567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9482110403270178967374845 3555791401226317112765567)
                      ·
                        rfl

theorem cell23_6924879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 3, 1, 3, 3].length) (baseStart_6924879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6924879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6924879 prefixEnd_6924879 := by exact prefixLift 6924879
  have htrace : WordTrace (prefixWord ++ tailWord_6924879) baseStart_6924879 baseEnd_6924879 := by
    simpa [prefixWord, tailWord_6924879, baseEnd_6924879] using wordTrace_append hprefix tailTrace_6924879
  have hstable : (prefixWord ++ tailWord_6924879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6924879).length < 2 ^ (prefixWord ++ tailWord_6924879).sum := by decide
  have hdescent : baseEnd_6924879 < baseStart_6924879 := by decide
  rcases family_descends (prefixWord ++ tailWord_6924879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6924894 : List Nat := [4, 4, 1, 2, 1, 2, 2, 1, 1, 5]
def baseStart_6924894 : Nat := 118140960795 + 6924894 * 2 ^ 59
def prefixEnd_6924894 : Nat := 4983230072969 + 3 ^ 40 * 6924894 * 2
def baseEnd_6924894 : Nat := 1185266367812044851359333

theorem tailTrace_6924894 : CollatzResearch.WordTrace tailWord_6924894 prefixEnd_6924894 1185266367812044851359333 := by
  unfold tailWord_6924894
  simp only [CollatzResearch.WordTrace]
  refine ⟨31571454221787398822815717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168381089182866127055017157 31571454221787398822815717)
  ·
    refine ⟨5919647666585137279277947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31571454221787398822815717 5919647666585137279277947)
    ·
      refine ⟨8879471499877705918916921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5919647666585137279277947 8879471499877705918916921)
      ·
        refine ⟨6659603624908279439187691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8879471499877705918916921 6659603624908279439187691)
        ·
          refine ⟨9989405437362419158781537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6659603624908279439187691 9989405437362419158781537)
          ·
            refine ⟨7492054078021814369086153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9989405437362419158781537 7492054078021814369086153)
            ·
              refine ⟨5619040558516360776814615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7492054078021814369086153 5619040558516360776814615)
              ·
                refine ⟨8428560837774541165221923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5619040558516360776814615 8428560837774541165221923)
                ·
                  refine ⟨12642841256661811747832885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8428560837774541165221923 12642841256661811747832885)
                  ·
                    refine ⟨1185266367812044851359333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12642841256661811747832885 1185266367812044851359333)
                    ·
                      rfl

theorem cell23_6924894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_6924894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6924894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6924894 prefixEnd_6924894 := by exact prefixLift 6924894
  have htrace : WordTrace (prefixWord ++ tailWord_6924894) baseStart_6924894 baseEnd_6924894 := by
    simpa [prefixWord, tailWord_6924894, baseEnd_6924894] using wordTrace_append hprefix tailTrace_6924894
  have hstable : (prefixWord ++ tailWord_6924894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6924894).length < 2 ^ (prefixWord ++ tailWord_6924894).sum := by decide
  have hdescent : baseEnd_6924894 < baseStart_6924894 := by decide
  rcases family_descends (prefixWord ++ tailWord_6924894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6924929 : List Nat := [1, 2, 4, 2, 1, 1, 1, 3, 2, 6]
def baseStart_6924929 : Nat := 118140960795 + 6924929 * 2 ^ 59
def prefixEnd_6924929 : Nat := 4983230072969 + 3 ^ 40 * 6924929 * 2
def baseEnd_6924929 : Nat := 1185272358419680639046779

theorem tailTrace_6924929 : CollatzResearch.WordTrace tailWord_6924929 prefixEnd_6924929 1185272358419680639046779 := by
  unfold tailWord_6924929
  simp only [CollatzResearch.WordTrace]
  refine ⟨252572910329172391560049841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168381940219448261040033227 252572910329172391560049841)
  ·
    refine ⟨189429682746879293670037381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252572910329172391560049841 189429682746879293670037381)
    ·
      refine ⟨35518065515039867563132009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 189429682746879293670037381 35518065515039867563132009)
      ·
        refine ⟨26638549136279900672349007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35518065515039867563132009 26638549136279900672349007)
        ·
          refine ⟨39957823704419851008523511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26638549136279900672349007 39957823704419851008523511)
          ·
            refine ⟨59936735556629776512785267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39957823704419851008523511 59936735556629776512785267)
            ·
              refine ⟨89905103334944664769177901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59936735556629776512785267 89905103334944664769177901)
              ·
                refine ⟨33714413750604249288441713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89905103334944664769177901 33714413750604249288441713)
                ·
                  refine ⟨25285810312953186966331285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33714413750604249288441713 25285810312953186966331285)
                  ·
                    refine ⟨1185272358419680639046779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25285810312953186966331285 1185272358419680639046779)
                    ·
                      rfl

theorem cell23_6924929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_6924929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6924929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6924929 prefixEnd_6924929 := by exact prefixLift 6924929
  have htrace : WordTrace (prefixWord ++ tailWord_6924929) baseStart_6924929 baseEnd_6924929 := by
    simpa [prefixWord, tailWord_6924929, baseEnd_6924929] using wordTrace_append hprefix tailTrace_6924929
  have hstable : (prefixWord ++ tailWord_6924929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6924929).length < 2 ^ (prefixWord ++ tailWord_6924929).sum := by decide
  have hdescent : baseEnd_6924929 < baseStart_6924929 := by decide
  rcases family_descends (prefixWord ++ tailWord_6924929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6924956 : List Nat := [2, 2, 3, 2, 2, 2, 1, 1, 2, 1, 5]
def baseStart_6924956 : Nat := 118140960795 + 6924956 * 2 ^ 59
def prefixEnd_6924956 : Nat := 4983230072969 + 3 ^ 40 * 6924956 * 2
def baseEnd_6924956 : Nat := 3555830939236713311502713

theorem tailTrace_6924956 : CollatzResearch.WordTrace tailWord_6924956 prefixEnd_6924956 3555830939236713311502713 := by
  unfold tailWord_6924956
  simp only [CollatzResearch.WordTrace]
  refine ⟨126286947550037287585641361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168382596733383050114188481 126286947550037287585641361)
  ·
    refine ⟨94715210662527965689231021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126286947550037287585641361 94715210662527965689231021)
    ·
      refine ⟨35518203998447987133461633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94715210662527965689231021 35518203998447987133461633)
      ·
        refine ⟨26638652998835990350096225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35518203998447987133461633 26638652998835990350096225)
        ·
          refine ⟨19978989749126992762572169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26638652998835990350096225 19978989749126992762572169)
          ·
            refine ⟨14984242311845244571929127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19978989749126992762572169 14984242311845244571929127)
            ·
              refine ⟨22476363467767866857893691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14984242311845244571929127 22476363467767866857893691)
              ·
                refine ⟨33714545201651800286840537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22476363467767866857893691 33714545201651800286840537)
                ·
                  refine ⟨25285908901238850215130403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33714545201651800286840537 25285908901238850215130403)
                  ·
                    refine ⟨37928863351858275322695605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25285908901238850215130403 37928863351858275322695605)
                    ·
                      refine ⟨3555830939236713311502713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37928863351858275322695605 3555830939236713311502713)
                      ·
                        rfl

theorem cell23_6924956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_6924956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6924956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6924956 prefixEnd_6924956 := by exact prefixLift 6924956
  have htrace : WordTrace (prefixWord ++ tailWord_6924956) baseStart_6924956 baseEnd_6924956 := by
    simpa [prefixWord, tailWord_6924956, baseEnd_6924956] using wordTrace_append hprefix tailTrace_6924956
  have hstable : (prefixWord ++ tailWord_6924956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6924956).length < 2 ^ (prefixWord ++ tailWord_6924956).sum := by decide
  have hdescent : baseEnd_6924956 < baseStart_6924956 := by decide
  rcases family_descends (prefixWord ++ tailWord_6924956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6925006 : List Nat := [4, 1, 1, 1, 3, 2, 1, 3, 2, 5]
def baseStart_6925006 : Nat := 118140960795 + 6925006 * 2 ^ 59
def prefixEnd_6925006 : Nat := 4983230072969 + 3 ^ 40 * 6925006 * 2
def baseEnd_6925006 : Nat := 1185285537756479371959161

theorem tailTrace_6925006 : CollatzResearch.WordTrace tailWord_6925006 prefixEnd_6925006 1185285537756479371959161 := by
  unfold tailWord_6925006
  simp only [CollatzResearch.WordTrace]
  refine ⟨31571964843736679213825359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168383812499928955807068581 31571964843736679213825359)
  ·
    refine ⟨47357947265605018820738039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31571964843736679213825359 47357947265605018820738039)
    ·
      refine ⟨71036920898407528231107059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47357947265605018820738039 71036920898407528231107059)
      ·
        refine ⟨106555381347611292346660589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71036920898407528231107059 106555381347611292346660589)
        ·
          refine ⟨39958268005354234629997721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106555381347611292346660589 39958268005354234629997721)
          ·
            refine ⟨29968701004015675972498291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39958268005354234629997721 29968701004015675972498291)
            ·
              refine ⟨44953051506023513958747437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29968701004015675972498291 44953051506023513958747437)
              ·
                refine ⟨16857394314758817734530289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44953051506023513958747437 16857394314758817734530289)
                ·
                  refine ⟨12643045736069113300897717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16857394314758817734530289 12643045736069113300897717)
                  ·
                    refine ⟨1185285537756479371959161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12643045736069113300897717 1185285537756479371959161)
                    ·
                      rfl

theorem cell23_6925006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 3, 2, 5].length) (baseStart_6925006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6925006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6925006 prefixEnd_6925006 := by exact prefixLift 6925006
  have htrace : WordTrace (prefixWord ++ tailWord_6925006) baseStart_6925006 baseEnd_6925006 := by
    simpa [prefixWord, tailWord_6925006, baseEnd_6925006] using wordTrace_append hprefix tailTrace_6925006
  have hstable : (prefixWord ++ tailWord_6925006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6925006).length < 2 ^ (prefixWord ++ tailWord_6925006).sum := by decide
  have hdescent : baseEnd_6925006 < baseStart_6925006 := by decide
  rcases family_descends (prefixWord ++ tailWord_6925006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6925036 : List Nat := [2, 2, 1, 1, 2, 2, 1, 5, 3, 4]
def baseStart_6925036 : Nat := 118140960795 + 6925036 * 2 ^ 59
def prefixEnd_6925036 : Nat := 4983230072969 + 3 ^ 40 * 6925036 * 2
def baseEnd_6925036 : Nat := 1185290672563024332834115

theorem tailTrace_6925036 : CollatzResearch.WordTrace tailWord_6925036 prefixEnd_6925036 1185290672563024332834115 := by
  unfold tailWord_6925036
  simp only [CollatzResearch.WordTrace]
  refine ⟨126288406469892374417097481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168384541959856499222796641 126288406469892374417097481)
  ·
    refine ⟨94716304852419280812823111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126288406469892374417097481 94716304852419280812823111)
    ·
      refine ⟨142074457278628921219234667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94716304852419280812823111 142074457278628921219234667)
      ·
        refine ⟨213111685917943381828852001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142074457278628921219234667 213111685917943381828852001)
        ·
          refine ⟨159833764438457536371639001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213111685917943381828852001 159833764438457536371639001)
          ·
            refine ⟨119875323328843152278729251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159833764438457536371639001 119875323328843152278729251)
            ·
              refine ⟨179812984993264728418093877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119875323328843152278729251 179812984993264728418093877)
              ·
                refine ⟨16857467343118568289196301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 179812984993264728418093877 16857467343118568289196301)
                ·
                  refine ⟨6321550253669463108448613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16857467343118568289196301 6321550253669463108448613)
                  ·
                    refine ⟨1185290672563024332834115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6321550253669463108448613 1185290672563024332834115)
                    ·
                      rfl

theorem cell23_6925036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 4].length) (baseStart_6925036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6925036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6925036 prefixEnd_6925036 := by exact prefixLift 6925036
  have htrace : WordTrace (prefixWord ++ tailWord_6925036) baseStart_6925036 baseEnd_6925036 := by
    simpa [prefixWord, tailWord_6925036, baseEnd_6925036] using wordTrace_append hprefix tailTrace_6925036
  have hstable : (prefixWord ++ tailWord_6925036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6925036).length < 2 ^ (prefixWord ++ tailWord_6925036).sum := by decide
  have hdescent : baseEnd_6925036 < baseStart_6925036 := by decide
  rcases family_descends (prefixWord ++ tailWord_6925036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6925063 : List Nat := [1, 1, 4, 4, 1, 2, 1, 1, 1, 4, 3]
def baseStart_6925063 : Nat := 118140960795 + 6925063 * 2 ^ 59
def prefixEnd_6925063 : Nat := 4983230072969 + 3 ^ 40 * 6925063 * 2
def baseEnd_6925063 : Nat := 3555885881666744392864721

theorem tailTrace_6925063 : CollatzResearch.WordTrace tailWord_6925063 prefixEnd_6925063 3555885881666744392864721 := by
  unfold tailWord_6925063
  simp only [CollatzResearch.WordTrace]
  refine ⟨252577797710686932445427843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168385198473791288296951895 252577797710686932445427843)
  ·
    refine ⟨378866696566030398668141765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252577797710686932445427843 378866696566030398668141765)
    ·
      refine ⟨71037505606130699750276581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 378866696566030398668141765 71037505606130699750276581)
      ·
        refine ⟨13319532301149506203176859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71037505606130699750276581 13319532301149506203176859)
        ·
          refine ⟨19979298451724259304765289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13319532301149506203176859 19979298451724259304765289)
          ·
            refine ⟨14984473838793194478573967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19979298451724259304765289 14984473838793194478573967)
            ·
              refine ⟨22476710758189791717860951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14984473838793194478573967 22476710758189791717860951)
              ·
                refine ⟨33715066137284687576791427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22476710758189791717860951 33715066137284687576791427)
                ·
                  refine ⟨50572599205927031365187141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33715066137284687576791427 50572599205927031365187141)
                  ·
                    refine ⟨9482362351111318380972589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50572599205927031365187141 9482362351111318380972589)
                    ·
                      refine ⟨3555885881666744392864721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9482362351111318380972589 3555885881666744392864721)
                      ·
                        rfl

theorem cell23_6925063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_6925063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6925063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6925063 prefixEnd_6925063 := by exact prefixLift 6925063
  have htrace : WordTrace (prefixWord ++ tailWord_6925063) baseStart_6925063 baseEnd_6925063 := by
    simpa [prefixWord, tailWord_6925063, baseEnd_6925063] using wordTrace_append hprefix tailTrace_6925063
  have hstable : (prefixWord ++ tailWord_6925063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6925063).length < 2 ^ (prefixWord ++ tailWord_6925063).sum := by decide
  have hdescent : baseEnd_6925063 < baseStart_6925063 := by decide
  rcases family_descends (prefixWord ++ tailWord_6925063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6925121 : List Nat := [1, 2, 5, 3, 2, 1, 1, 3, 1, 4]
def baseStart_6925121 : Nat := 118140960795 + 6925121 * 2 ^ 59
def prefixEnd_6925121 : Nat := 4983230072969 + 3 ^ 40 * 6925121 * 2
def baseEnd_6925121 : Nat := 1185305221181568388646485

theorem tailTrace_6925121 : CollatzResearch.WordTrace tailWord_6925121 prefixEnd_6925121 1185305221181568388646485 := by
  unfold tailWord_6925121
  simp only [CollatzResearch.WordTrace]
  refine ⟨252579913144476808351039217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168386608762984538900692811 252579913144476808351039217)
  ·
    refine ⟨189434934858357606263279413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252579913144476808351039217 189434934858357606263279413)
    ·
      refine ⟨17759525142971025587182445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 189434934858357606263279413 17759525142971025587182445)
      ·
        refine ⟨6659821928614134595193417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17759525142971025587182445 6659821928614134595193417)
        ·
          refine ⟨4994866446460600946395063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6659821928614134595193417 4994866446460600946395063)
          ·
            refine ⟨7492299669690901419592595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4994866446460600946395063 7492299669690901419592595)
            ·
              refine ⟨11238449504536352129388893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7492299669690901419592595 11238449504536352129388893)
              ·
                refine ⟨4214418564201132048520835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11238449504536352129388893 4214418564201132048520835)
                ·
                  refine ⟨6321627846301698072781253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4214418564201132048520835 6321627846301698072781253)
                  ·
                    refine ⟨1185305221181568388646485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6321627846301698072781253 1185305221181568388646485)
                    ·
                      rfl

theorem cell23_6925121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_6925121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6925121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6925121 prefixEnd_6925121 := by exact prefixLift 6925121
  have htrace : WordTrace (prefixWord ++ tailWord_6925121) baseStart_6925121 baseEnd_6925121 := by
    simpa [prefixWord, tailWord_6925121, baseEnd_6925121] using wordTrace_append hprefix tailTrace_6925121
  have hstable : (prefixWord ++ tailWord_6925121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6925121).length < 2 ^ (prefixWord ++ tailWord_6925121).sum := by decide
  have hdescent : baseEnd_6925121 < baseStart_6925121 := by decide
  rcases family_descends (prefixWord ++ tailWord_6925121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6925136 : List Nat := [2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 5]
def baseStart_6925136 : Nat := 118140960795 + 6925136 * 2 ^ 59
def prefixEnd_6925136 : Nat := 4983230072969 + 3 ^ 40 * 6925136 * 2
def baseEnd_6925136 : Nat := 3555923365754522607251885

theorem tailTrace_6925136 : CollatzResearch.WordTrace tailWord_6925136 prefixEnd_6925136 3555923365754522607251885 := by
  unfold tailWord_6925136
  simp only [CollatzResearch.WordTrace]
  refine ⟨126290230119711232956417631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168386973492948310608556841 126290230119711232956417631)
  ·
    refine ⟨189435345179566849434626447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126290230119711232956417631 189435345179566849434626447)
    ·
      refine ⟨284153017769350274151939671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189435345179566849434626447 284153017769350274151939671)
      ·
        refine ⟨426229526654025411227909507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284153017769350274151939671 426229526654025411227909507)
        ·
          refine ⟨639344289981038116841864261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426229526654025411227909507 639344289981038116841864261)
          ·
            refine ⟨119877054371444646907849549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 639344289981038116841864261 119877054371444646907849549)
            ·
              refine ⟨44953895389291742590443581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119877054371444646907849549 44953895389291742590443581)
              ·
                refine ⟨16857710770984403471416343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44953895389291742590443581 16857710770984403471416343)
                ·
                  refine ⟨25286566156476605207124515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16857710770984403471416343 25286566156476605207124515)
                  ·
                    refine ⟨37929849234714907810686773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25286566156476605207124515 37929849234714907810686773)
                    ·
                      refine ⟨3555923365754522607251885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37929849234714907810686773 3555923365754522607251885)
                      ·
                        rfl

theorem cell23_6925136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 5].length) (baseStart_6925136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6925136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6925136 prefixEnd_6925136 := by exact prefixLift 6925136
  have htrace : WordTrace (prefixWord ++ tailWord_6925136) baseStart_6925136 baseEnd_6925136 := by
    simpa [prefixWord, tailWord_6925136, baseEnd_6925136] using wordTrace_append hprefix tailTrace_6925136
  have hstable : (prefixWord ++ tailWord_6925136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6925136).length < 2 ^ (prefixWord ++ tailWord_6925136).sum := by decide
  have hdescent : baseEnd_6925136 < baseStart_6925136 := by decide
  rcases family_descends (prefixWord ++ tailWord_6925136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6925143 : List Nat := [1, 1, 3, 2, 4, 1, 2, 1, 4, 4]
def baseStart_6925143 : Nat := 118140960795 + 6925143 * 2 ^ 59
def prefixEnd_6925143 : Nat := 4983230072969 + 3 ^ 40 * 6925143 * 2
def baseEnd_6925143 : Nat := 1185308986706368026621451

theorem tailTrace_6925143 : CollatzResearch.WordTrace tailWord_6925143 prefixEnd_6925143 1185308986706368026621451 := by
  unfold tailWord_6925143
  simp only [CollatzResearch.WordTrace]
  refine ⟨252580715550397106108340083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168387143700264737405560055 252580715550397106108340083)
  ·
    refine ⟨378871073325595659162510125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252580715550397106108340083 378871073325595659162510125)
    ·
      refine ⟨142076652497098372185941297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 378871073325595659162510125 142076652497098372185941297)
      ·
        refine ⟨106557489372823779139455973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142076652497098372185941297 106557489372823779139455973)
        ·
          refine ⟨19979529257404458588647995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106557489372823779139455973 19979529257404458588647995)
          ·
            refine ⟨29969293886106687882971993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19979529257404458588647995 29969293886106687882971993)
            ·
              refine ⟨22476970414580015912228995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29969293886106687882971993 22476970414580015912228995)
              ·
                refine ⟨33715455621870023868343493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22476970414580015912228995 33715455621870023868343493)
                ·
                  refine ⟨6321647929100629475314405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33715455621870023868343493 6321647929100629475314405)
                  ·
                    refine ⟨1185308986706368026621451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6321647929100629475314405 1185308986706368026621451)
                    ·
                      rfl

theorem cell23_6925143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 4, 4].length) (baseStart_6925143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6925143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6925143 prefixEnd_6925143 := by exact prefixLift 6925143
  have htrace : WordTrace (prefixWord ++ tailWord_6925143) baseStart_6925143 baseEnd_6925143 := by
    simpa [prefixWord, tailWord_6925143, baseEnd_6925143] using wordTrace_append hprefix tailTrace_6925143
  have hstable : (prefixWord ++ tailWord_6925143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6925143).length < 2 ^ (prefixWord ++ tailWord_6925143).sum := by decide
  have hdescent : baseEnd_6925143 < baseStart_6925143 := by decide
  rcases family_descends (prefixWord ++ tailWord_6925143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6925146 : List Nat := [3, 1, 1, 2, 1, 4, 1, 2, 1, 1, 6]
def baseStart_6925146 : Nat := 118140960795 + 6925146 * 2 ^ 59
def prefixEnd_6925146 : Nat := 4983230072969 + 3 ^ 40 * 6925146 * 2
def baseEnd_6925146 : Nat := 3555928500561067568126839

theorem tailTrace_6925146 : CollatzResearch.WordTrace tailWord_6925146 prefixEnd_6925146 3555928500561067568126839 := by
  unfold tailWord_6925146
  simp only [CollatzResearch.WordTrace]
  refine ⟨63145206242346559405174823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168387216646257491747132861 63145206242346559405174823)
  ·
    refine ⟨94717809363519839107762235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63145206242346559405174823 94717809363519839107762235)
    ·
      refine ⟨142076714045279758661643353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94717809363519839107762235 142076714045279758661643353)
      ·
        refine ⟨106557535533959818996232515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142076714045279758661643353 106557535533959818996232515)
        ·
          refine ⟨159836303300939728494348773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106557535533959818996232515 159836303300939728494348773)
          ·
            refine ⟨29969306868926199092690395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 159836303300939728494348773 29969306868926199092690395)
            ·
              refine ⟨44953960303389298639035593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29969306868926199092690395 44953960303389298639035593)
              ·
                refine ⟨33715470227541973979276695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44953960303389298639035593 33715470227541973979276695)
                ·
                  refine ⟨50573205341312960968915043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33715470227541973979276695 50573205341312960968915043)
                  ·
                    refine ⟨75859808011969441453372565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50573205341312960968915043 75859808011969441453372565)
                    ·
                      refine ⟨3555928500561067568126839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75859808011969441453372565 3555928500561067568126839)
                      ·
                        rfl

theorem cell23_6925146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 1, 1, 6].length) (baseStart_6925146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6925146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6925146 prefixEnd_6925146 := by exact prefixLift 6925146
  have htrace : WordTrace (prefixWord ++ tailWord_6925146) baseStart_6925146 baseEnd_6925146 := by
    simpa [prefixWord, tailWord_6925146, baseEnd_6925146] using wordTrace_append hprefix tailTrace_6925146
  have hstable : (prefixWord ++ tailWord_6925146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6925146).length < 2 ^ (prefixWord ++ tailWord_6925146).sum := by decide
  have hdescent : baseEnd_6925146 < baseStart_6925146 := by decide
  rcases family_descends (prefixWord ++ tailWord_6925146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6925156 : List Nat := [2, 3, 1, 1, 4, 1, 1, 10]
def baseStart_6925156 : Nat := 118140960795 + 6925156 * 2 ^ 59
def prefixEnd_6925156 : Nat := 4983230072969 + 3 ^ 40 * 6925156 * 2
def baseEnd_6925156 : Nat := 131701245754356019592659

theorem tailTrace_6925156 : CollatzResearch.WordTrace tailWord_6925156 prefixEnd_6925156 131701245754356019592659 := by
  unfold tailWord_6925156
  simp only [CollatzResearch.WordTrace]
  refine ⟨126290594849675004664281661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168387459799566672885708881 126290594849675004664281661)
  ·
    refine ⟨47358973068628126749105623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126290594849675004664281661 47358973068628126749105623)
    ·
      refine ⟨71038459602942190123658435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47358973068628126749105623 71038459602942190123658435)
      ·
        refine ⟨106557689404413285185487653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71038459602942190123658435 106557689404413285185487653)
        ·
          refine ⟨19979566763327490972278935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106557689404413285185487653 19979566763327490972278935)
          ·
            refine ⟨29969350144991236458418403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19979566763327490972278935 29969350144991236458418403)
            ·
              refine ⟨44954025217486854687627605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29969350144991236458418403 44954025217486854687627605)
              ·
                refine ⟨131701245754356019592659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 44954025217486854687627605 131701245754356019592659)
                ·
                  rfl

theorem cell23_6925156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 10].length) (baseStart_6925156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6925156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6925156 prefixEnd_6925156 := by exact prefixLift 6925156
  have htrace : WordTrace (prefixWord ++ tailWord_6925156) baseStart_6925156 baseEnd_6925156 := by
    simpa [prefixWord, tailWord_6925156, baseEnd_6925156] using wordTrace_append hprefix tailTrace_6925156
  have hstable : (prefixWord ++ tailWord_6925156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6925156).length < 2 ^ (prefixWord ++ tailWord_6925156).sum := by decide
  have hdescent : baseEnd_6925156 < baseStart_6925156 := by decide
  rcases family_descends (prefixWord ++ tailWord_6925156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6925160 : List Nat := [2, 1, 4, 2, 1, 3, 1, 3, 2, 4]
def baseStart_6925160 : Nat := 118140960795 + 6925160 * 2 ^ 59
def prefixEnd_6925160 : Nat := 4983230072969 + 3 ^ 40 * 6925160 * 2
def baseEnd_6925160 : Nat := 1185311896430076837783925

theorem tailTrace_6925160 : CollatzResearch.WordTrace tailWord_6925160 prefixEnd_6925160 1185311896430076837783925 := by
  unfold tailWord_6925160
  simp only [CollatzResearch.WordTrace]
  refine ⟨126290667795667759005854467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168387557060890345341139289 126290667795667759005854467)
  ·
    refine ⟨189436001693501638508781701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126290667795667759005854467 189436001693501638508781701)
    ·
      refine ⟨35519250317531557220396569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 189436001693501638508781701 35519250317531557220396569)
      ·
        refine ⟨26639437738148667915297427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35519250317531557220396569 26639437738148667915297427)
        ·
          refine ⟨39959156607223001872946141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26639437738148667915297427 39959156607223001872946141)
          ·
            refine ⟨14984683727708625702354803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39959156607223001872946141 14984683727708625702354803)
            ·
              refine ⟨22477025591562938553532205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14984683727708625702354803 22477025591562938553532205)
              ·
                refine ⟨8428884596836101957574577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22477025591562938553532205 8428884596836101957574577)
                ·
                  refine ⟨6321663447627076468180933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8428884596836101957574577 6321663447627076468180933)
                  ·
                    refine ⟨1185311896430076837783925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6321663447627076468180933 1185311896430076837783925)
                    ·
                      rfl

theorem cell23_6925160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 3, 2, 4].length) (baseStart_6925160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6925160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6925160 prefixEnd_6925160 := by exact prefixLift 6925160
  have htrace : WordTrace (prefixWord ++ tailWord_6925160) baseStart_6925160 baseEnd_6925160 := by
    simpa [prefixWord, tailWord_6925160, baseEnd_6925160] using wordTrace_append hprefix tailTrace_6925160
  have hstable : (prefixWord ++ tailWord_6925160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6925160).length < 2 ^ (prefixWord ++ tailWord_6925160).sum := by decide
  have hdescent : baseEnd_6925160 < baseStart_6925160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6925160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6925170 : List Nat := [3, 2, 1, 2, 1, 1, 5, 2, 1, 2, 3]
def baseStart_6925170 : Nat := 118140960795 + 6925170 * 2 ^ 59
def prefixEnd_6925170 : Nat := 4983230072969 + 3 ^ 40 * 6925170 * 2
def baseEnd_6925170 : Nat := 3555940824096775474226729

theorem tailTrace_6925170 : CollatzResearch.WordTrace tailWord_6925170 prefixEnd_6925170 3555940824096775474226729 := by
  unfold tailWord_6925170
  simp only [CollatzResearch.WordTrace]
  refine ⟨63145425080324822429893241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168387800214199526479715309 63145425080324822429893241)
  ·
    refine ⟨47359068810243616822419931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63145425080324822429893241 47359068810243616822419931)
    ·
      refine ⟨71038603215365425233629897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47359068810243616822419931 71038603215365425233629897)
      ·
        refine ⟨53278952411524068925222423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71038603215365425233629897 53278952411524068925222423)
        ·
          refine ⟨79918428617286103387833635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53278952411524068925222423 79918428617286103387833635)
          ·
            refine ⟨119877642925929155081750453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79918428617286103387833635 119877642925929155081750453)
            ·
              refine ⟨11238529024305858288914105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 119877642925929155081750453 11238529024305858288914105)
              ·
                refine ⟨8428896768229393716685579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11238529024305858288914105 8428896768229393716685579)
                ·
                  refine ⟨12643345152344090575028369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8428896768229393716685579 12643345152344090575028369)
                  ·
                    refine ⟨9482508864258067931271277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12643345152344090575028369 9482508864258067931271277)
                    ·
                      refine ⟨3555940824096775474226729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9482508864258067931271277 3555940824096775474226729)
                      ·
                        rfl

theorem cell23_6925170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 2, 1, 2, 3].length) (baseStart_6925170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6925170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6925170 prefixEnd_6925170 := by exact prefixLift 6925170
  have htrace : WordTrace (prefixWord ++ tailWord_6925170) baseStart_6925170 baseEnd_6925170 := by
    simpa [prefixWord, tailWord_6925170, baseEnd_6925170] using wordTrace_append hprefix tailTrace_6925170
  have hstable : (prefixWord ++ tailWord_6925170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6925170).length < 2 ^ (prefixWord ++ tailWord_6925170).sum := by decide
  have hdescent : baseEnd_6925170 < baseStart_6925170 := by decide
  rcases family_descends (prefixWord ++ tailWord_6925170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6925183 : List Nat := [1, 1, 2, 2, 1, 1, 4, 1, 6, 1, 3]
def baseStart_6925183 : Nat := 118140960795 + 6925183 * 2 ^ 59
def prefixEnd_6925183 : Nat := 4983230072969 + 3 ^ 40 * 6925183 * 2
def baseEnd_6925183 : Nat := 3555947499345283923364169

theorem tailTrace_6925183 : CollatzResearch.WordTrace tailWord_6925183 prefixEnd_6925183 3555947499345283923364169 := by
  unfold tailWord_6925183
  simp only [CollatzResearch.WordTrace]
  refine ⟨252582174470252192939796203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168388116313501461959864135 252582174470252192939796203)
  ·
    refine ⟨378873261705378289409694305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252582174470252192939796203 378873261705378289409694305)
    ·
      refine ⟨284154946279033717057270729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 378873261705378289409694305 284154946279033717057270729)
      ·
        refine ⟨213116209709275287792953047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 284154946279033717057270729 213116209709275287792953047)
        ·
          refine ⟨319674314563912931689429571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213116209709275287792953047 319674314563912931689429571)
          ·
            refine ⟨479511471845869397534144357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319674314563912931689429571 479511471845869397534144357)
            ·
              refine ⟨89908400971100512037652067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 479511471845869397534144357 89908400971100512037652067)
              ·
                refine ⟨134862601456650768056478101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89908400971100512037652067 134862601456650768056478101)
                ·
                  refine ⟨6321684443280504752647411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 134862601456650768056478101 6321684443280504752647411)
                  ·
                    refine ⟨9482526664920757128971117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6321684443280504752647411 9482526664920757128971117)
                    ·
                      refine ⟨3555947499345283923364169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9482526664920757128971117 3555947499345283923364169)
                      ·
                        rfl

theorem cell23_6925183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 6, 1, 3].length) (baseStart_6925183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6925183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6925183 prefixEnd_6925183 := by exact prefixLift 6925183
  have htrace : WordTrace (prefixWord ++ tailWord_6925183) baseStart_6925183 baseEnd_6925183 := by
    simpa [prefixWord, tailWord_6925183, baseEnd_6925183] using wordTrace_append hprefix tailTrace_6925183
  have hstable : (prefixWord ++ tailWord_6925183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6925183).length < 2 ^ (prefixWord ++ tailWord_6925183).sum := by decide
  have hdescent : baseEnd_6925183 < baseStart_6925183 := by decide
  rcases family_descends (prefixWord ++ tailWord_6925183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6925196 : List Nat := [2, 2, 1, 2, 1, 2, 2, 2, 2, 2, 5]
def baseStart_6925196 : Nat := 118140960795 + 6925196 * 2 ^ 59
def prefixEnd_6925196 : Nat := 4983230072969 + 3 ^ 40 * 6925196 * 2
def baseEnd_6925196 : Nat := 3555954174593792372501609

theorem tailTrace_6925196 : CollatzResearch.WordTrace tailWord_6925196 prefixEnd_6925196 3555954174593792372501609 := by
  unfold tailWord_6925196
  simp only [CollatzResearch.WordTrace]
  refine ⟨126291324309602548080009721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168388432412803397440012961 126291324309602548080009721)
  ·
    refine ⟨94718493232201911060007291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126291324309602548080009721 94718493232201911060007291)
    ·
      refine ⟨142077739848302866590010937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94718493232201911060007291 142077739848302866590010937)
      ·
        refine ⟨106558304886227149942508203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142077739848302866590010937 106558304886227149942508203)
        ·
          refine ⟨159837457329340724913762305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106558304886227149942508203 159837457329340724913762305)
          ·
            refine ⟨119878092997005543685321729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159837457329340724913762305 119878092997005543685321729)
            ·
              refine ⟨89908569747754157763991297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119878092997005543685321729 89908569747754157763991297)
              ·
                refine ⟨67431427310815618322993473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89908569747754157763991297 67431427310815618322993473)
                ·
                  refine ⟨50573570483111713742245105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67431427310815618322993473 50573570483111713742245105)
                  ·
                    refine ⟨37930177862333785306683829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50573570483111713742245105 37930177862333785306683829)
                    ·
                      refine ⟨3555954174593792372501609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37930177862333785306683829 3555954174593792372501609)
                      ·
                        rfl

theorem cell23_6925196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_6925196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6925196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6925196 prefixEnd_6925196 := by exact prefixLift 6925196
  have htrace : WordTrace (prefixWord ++ tailWord_6925196) baseStart_6925196 baseEnd_6925196 := by
    simpa [prefixWord, tailWord_6925196, baseEnd_6925196] using wordTrace_append hprefix tailTrace_6925196
  have hstable : (prefixWord ++ tailWord_6925196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6925196).length < 2 ^ (prefixWord ++ tailWord_6925196).sum := by decide
  have hdescent : baseEnd_6925196 < baseStart_6925196 := by decide
  rcases family_descends (prefixWord ++ tailWord_6925196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6925216 : List Nat := [2, 1, 1, 4, 1, 1, 3, 1, 1, 8]
def baseStart_6925216 : Nat := 118140960795 + 6925216 * 2 ^ 59
def prefixEnd_6925216 : Nat := 4983230072969 + 3 ^ 40 * 6925216 * 2
def baseEnd_6925216 : Nat := 1185321481402294098083839

theorem tailTrace_6925216 : CollatzResearch.WordTrace tailWord_6925216 prefixEnd_6925216 1185321481402294098083839 := by
  unfold tailWord_6925216
  simp only [CollatzResearch.WordTrace]
  refine ⟨126291689039566319787873751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168388918719421759717165001 126291689039566319787873751)
  ·
    refine ⟨189437533559349479681810627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126291689039566319787873751 189437533559349479681810627)
    ·
      refine ⟨284156300339024219522715941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189437533559349479681810627 284156300339024219522715941)
      ·
        refine ⟨53279306313567041160509239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 284156300339024219522715941 53279306313567041160509239)
        ·
          refine ⟨79918959470350561740763859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53279306313567041160509239 79918959470350561740763859)
          ·
            refine ⟨119878439205525842611145789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79918959470350561740763859 119878439205525842611145789)
            ·
              refine ⟨44954414702072190979179671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119878439205525842611145789 44954414702072190979179671)
              ·
                refine ⟨67431622053108286468769507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44954414702072190979179671 67431622053108286468769507)
                ·
                  refine ⟨101147433079662429703154261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67431622053108286468769507 101147433079662429703154261)
                  ·
                    refine ⟨1185321481402294098083839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 101147433079662429703154261 1185321481402294098083839)
                    ·
                      rfl

theorem cell23_6925216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 1, 8].length) (baseStart_6925216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6925216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6925216 prefixEnd_6925216 := by exact prefixLift 6925216
  have htrace : WordTrace (prefixWord ++ tailWord_6925216) baseStart_6925216 baseEnd_6925216 := by
    simpa [prefixWord, tailWord_6925216, baseEnd_6925216] using wordTrace_append hprefix tailTrace_6925216
  have hstable : (prefixWord ++ tailWord_6925216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6925216).length < 2 ^ (prefixWord ++ tailWord_6925216).sum := by decide
  have hdescent : baseEnd_6925216 < baseStart_6925216 := by decide
  rcases family_descends (prefixWord ++ tailWord_6925216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6925217 : List Nat := [1, 2, 3, 4, 1, 1, 2, 3, 2, 1, 3]
def baseStart_6925217 : Nat := 118140960795 + 6925217 * 2 ^ 59
def prefixEnd_6925217 : Nat := 4983230072969 + 3 ^ 40 * 6925217 * 2
def baseEnd_6925217 : Nat := 3555964957687536790339013

theorem tailTrace_6925217 : CollatzResearch.WordTrace tailWord_6925217 prefixEnd_6925217 3555964957687536790339013 := by
  unfold tailWord_6925217
  simp only [CollatzResearch.WordTrace]
  refine ⟨252583414552129016746533905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168388943034752677831022603 252583414552129016746533905)
  ·
    refine ⟨189437560914096762559900429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252583414552129016746533905 189437560914096762559900429)
    ·
      refine ⟨71039085342786285959962661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189437560914096762559900429 71039085342786285959962661)
      ·
        refine ⟨13319828501772428617492999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71039085342786285959962661 13319828501772428617492999)
        ·
          refine ⟨19979742752658642926239499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13319828501772428617492999 19979742752658642926239499)
          ·
            refine ⟨29969614128987964389359249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19979742752658642926239499 29969614128987964389359249)
            ·
              refine ⟨22477210596740973292019437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29969614128987964389359249 22477210596740973292019437)
              ·
                refine ⟨8428953973777864984507289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22477210596740973292019437 8428953973777864984507289)
                ·
                  refine ⟨6321715480333398738380467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8428953973777864984507289 6321715480333398738380467)
                  ·
                    refine ⟨9482573220500098107570701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6321715480333398738380467 9482573220500098107570701)
                    ·
                      refine ⟨3555964957687536790339013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9482573220500098107570701 3555964957687536790339013)
                      ·
                        rfl

theorem cell23_6925217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_6925217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6925217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6925217 prefixEnd_6925217 := by exact prefixLift 6925217
  have htrace : WordTrace (prefixWord ++ tailWord_6925217) baseStart_6925217 baseEnd_6925217 := by
    simpa [prefixWord, tailWord_6925217, baseEnd_6925217] using wordTrace_append hprefix tailTrace_6925217
  have hstable : (prefixWord ++ tailWord_6925217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6925217).length < 2 ^ (prefixWord ++ tailWord_6925217).sum := by decide
  have hdescent : baseEnd_6925217 < baseStart_6925217 := by decide
  rcases family_descends (prefixWord ++ tailWord_6925217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6925240 : List Nat := [2, 1, 2, 1, 2, 4, 2, 2, 1, 4, 2]
def baseStart_6925240 : Nat := 118140960795 + 6925240 * 2 ^ 59
def prefixEnd_6925240 : Nat := 4983230072969 + 3 ^ 40 * 6925240 * 2
def baseEnd_6925240 : Nat := 3555976767742590200351407

theorem tailTrace_6925240 : CollatzResearch.WordTrace tailWord_6925240 prefixEnd_6925240 3555976767742590200351407 := by
  unfold tailWord_6925240
  simp only [CollatzResearch.WordTrace]
  refine ⟨126292126715522845837310587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168389502287363794449747449 126292126715522845837310587)
  ·
    refine ⟨189438190073284268755965881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126292126715522845837310587 189438190073284268755965881)
    ·
      refine ⟨142078642554963201566974411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189438190073284268755965881 142078642554963201566974411)
      ·
        refine ⟨213117963832444802350461617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142078642554963201566974411 213117963832444802350461617)
        ·
          refine ⟨159838472874333601762846213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213117963832444802350461617 159838472874333601762846213)
          ·
            refine ⟨29969713663937550330533665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 159838472874333601762846213 29969713663937550330533665)
            ·
              refine ⟨22477285247953162747900249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29969713663937550330533665 22477285247953162747900249)
              ·
                refine ⟨16857963935964872060925187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22477285247953162747900249 16857963935964872060925187)
                ·
                  refine ⟨25286945903947308091387781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16857963935964872060925187 25286945903947308091387781)
                  ·
                    refine ⟨4741302356990120267135209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25286945903947308091387781 4741302356990120267135209)
                    ·
                      refine ⟨3555976767742590200351407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4741302356990120267135209 3555976767742590200351407)
                      ·
                        rfl

theorem cell23_6925240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 2, 1, 4, 2].length) (baseStart_6925240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6925240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6925240 prefixEnd_6925240 := by exact prefixLift 6925240
  have htrace : WordTrace (prefixWord ++ tailWord_6925240) baseStart_6925240 baseEnd_6925240 := by
    simpa [prefixWord, tailWord_6925240, baseEnd_6925240] using wordTrace_append hprefix tailTrace_6925240
  have hstable : (prefixWord ++ tailWord_6925240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6925240).length < 2 ^ (prefixWord ++ tailWord_6925240).sum := by decide
  have hdescent : baseEnd_6925240 < baseStart_6925240 := by decide
  rcases family_descends (prefixWord ++ tailWord_6925240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6925263 : List Nat := [1, 1, 2, 1, 1, 7, 2, 1, 7]
def baseStart_6925263 : Nat := 118140960795 + 6925263 * 2 ^ 59
def prefixEnd_6925263 : Nat := 4983230072969 + 3 ^ 40 * 6925263 * 2
def baseEnd_6925263 : Nat := 395109841977515956707089

theorem tailTrace_6925263 : CollatzResearch.WordTrace tailWord_6925263 prefixEnd_6925263 395109841977515956707089 := by
  unfold tailWord_6925263
  simp only [CollatzResearch.WordTrace]
  refine ⟨252585092309962366602708443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168390061539974911068472295 252585092309962366602708443)
  ·
    refine ⟨378877638464943549904062665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252585092309962366602708443 378877638464943549904062665)
    ·
      refine ⟨284158228848707662428046999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 378877638464943549904062665 284158228848707662428046999)
      ·
        refine ⟨426237343273061493642070499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284158228848707662428046999 426237343273061493642070499)
        ·
          refine ⟨639356014909592240463105749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426237343273061493642070499 639356014909592240463105749)
          ·
            refine ⟨14984906599443568135854041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 639356014909592240463105749 14984906599443568135854041)
            ·
              refine ⟨11238679949582676101890531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14984906599443568135854041 11238679949582676101890531)
              ·
                refine ⟨16858019924374014152835797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11238679949582676101890531 16858019924374014152835797)
                ·
                  refine ⟨395109841977515956707089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16858019924374014152835797 395109841977515956707089)
                  ·
                    rfl

theorem cell23_6925263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 1, 7].length) (baseStart_6925263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6925263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6925263 prefixEnd_6925263 := by exact prefixLift 6925263
  have htrace : WordTrace (prefixWord ++ tailWord_6925263) baseStart_6925263 baseEnd_6925263 := by
    simpa [prefixWord, tailWord_6925263, baseEnd_6925263] using wordTrace_append hprefix tailTrace_6925263
  have hstable : (prefixWord ++ tailWord_6925263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6925263).length < 2 ^ (prefixWord ++ tailWord_6925263).sum := by decide
  have hdescent : baseEnd_6925263 < baseStart_6925263 := by decide
  rcases family_descends (prefixWord ++ tailWord_6925263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6925297 : List Nat := [1, 2, 2, 2, 4, 3, 1, 3, 5]
def baseStart_6925297 : Nat := 118140960795 + 6925297 * 2 ^ 59
def prefixEnd_6925297 : Nat := 4983230072969 + 3 ^ 40 * 6925297 * 2
def baseEnd_6925297 : Nat := 395111781793321830815405

theorem tailTrace_6925297 : CollatzResearch.WordTrace tailWord_6925297 prefixEnd_6925297 395111781793321830815405 := by
  unfold tailWord_6925297
  simp only [CollatzResearch.WordTrace]
  refine ⟨252586332391839190409446145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168390888261226126939630763 252586332391839190409446145)
  ·
    refine ⟨189439749293879392807084609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252586332391839190409446145 189439749293879392807084609)
    ·
      refine ⟨142079811970409544605313457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189439749293879392807084609 142079811970409544605313457)
      ·
        refine ⟨106559858977807158453985093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142079811970409544605313457 106559858977807158453985093)
        ·
          refine ⟨19979973558338842210122205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106559858977807158453985093 19979973558338842210122205)
          ·
            refine ⟨7492490084377065828795827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19979973558338842210122205 7492490084377065828795827)
            ·
              refine ⟨11238735126565598743193741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7492490084377065828795827 11238735126565598743193741)
              ·
                refine ⟨4214525672462099528697653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11238735126565598743193741 4214525672462099528697653)
                ·
                  refine ⟨395111781793321830815405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4214525672462099528697653 395111781793321830815405)
                  ·
                    rfl

theorem cell23_6925297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 3, 5].length) (baseStart_6925297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6925297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6925297 prefixEnd_6925297 := by exact prefixLift 6925297
  have htrace : WordTrace (prefixWord ++ tailWord_6925297) baseStart_6925297 baseEnd_6925297 := by
    simpa [prefixWord, tailWord_6925297, baseEnd_6925297] using wordTrace_append hprefix tailTrace_6925297
  have hstable : (prefixWord ++ tailWord_6925297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6925297).length < 2 ^ (prefixWord ++ tailWord_6925297).sum := by decide
  have hdescent : baseEnd_6925297 < baseStart_6925297 := by decide
  rcases family_descends (prefixWord ++ tailWord_6925297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6925314 : List Nat := [3, 4, 1, 3, 1, 2, 1, 1, 7]
def baseStart_6925314 : Nat := 118140960795 + 6925314 * 2 ^ 59
def prefixEnd_6925314 : Nat := 4983230072969 + 3 ^ 40 * 6925314 * 2
def baseEnd_6925314 : Nat := 395112751701224767869563

theorem tailTrace_6925314 : CollatzResearch.WordTrace tailWord_6925314 prefixEnd_6925314 395112751701224767869563 := by
  unfold tailWord_6925314
  simp only [CollatzResearch.WordTrace]
  refine ⟨63146738108194400578203749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168391301621851734875209997 63146738108194400578203749)
  ·
    refine ⟨11840013395286450108413203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63146738108194400578203749 11840013395286450108413203)
    ·
      refine ⟨17760020092929675162619805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11840013395286450108413203 17760020092929675162619805)
      ·
        refine ⟨6660007534848628185982427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17760020092929675162619805 6660007534848628185982427)
        ·
          refine ⟨9990011302272942278973641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6660007534848628185982427 9990011302272942278973641)
          ·
            refine ⟨7492508476704706709230231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9990011302272942278973641 7492508476704706709230231)
            ·
              refine ⟨11238762715057060063845347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7492508476704706709230231 11238762715057060063845347)
              ·
                refine ⟨16858144072585590095768021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11238762715057060063845347 16858144072585590095768021)
                ·
                  refine ⟨395112751701224767869563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16858144072585590095768021 395112751701224767869563)
                  ·
                    rfl

theorem cell23_6925314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_6925314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6925314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6925314 prefixEnd_6925314 := by exact prefixLift 6925314
  have htrace : WordTrace (prefixWord ++ tailWord_6925314) baseStart_6925314 baseEnd_6925314 := by
    simpa [prefixWord, tailWord_6925314, baseEnd_6925314] using wordTrace_append hprefix tailTrace_6925314
  have hstable : (prefixWord ++ tailWord_6925314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6925314).length < 2 ^ (prefixWord ++ tailWord_6925314).sum := by decide
  have hdescent : baseEnd_6925314 < baseStart_6925314 := by decide
  rcases family_descends (prefixWord ++ tailWord_6925314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6925397 : List Nat := [1, 3, 2, 2, 1, 2, 3, 2, 3, 1, 3]
def baseStart_6925397 : Nat := 118140960795 + 6925397 * 2 ^ 59
def prefixEnd_6925397 : Nat := 4983230072969 + 3 ^ 40 * 6925397 * 2
def baseEnd_6925397 : Nat := 3556057384205346086088185

theorem tailTrace_6925397 : CollatzResearch.WordTrace tailWord_6925397 prefixEnd_6925397 3556057384205346086088185 := by
  unfold tailWord_6925397
  simp only [CollatzResearch.WordTrace]
  refine ⟨252589979691476907488086445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168393319794317938325390963 252589979691476907488086445)
  ·
    refine ⟨94721242384303840308032417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252589979691476907488086445 94721242384303840308032417)
    ·
      refine ⟨71040931788227880231024313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94721242384303840308032417 71040931788227880231024313)
      ·
        refine ⟨53280698841170910173268235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71040931788227880231024313 53280698841170910173268235)
        ·
          refine ⟨79921048261756365259902353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53280698841170910173268235 79921048261756365259902353)
          ·
            refine ⟨59940786196317273944926765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79921048261756365259902353 59940786196317273944926765)
            ·
              refine ⟨22477794823618977729347537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59940786196317273944926765 22477794823618977729347537)
              ·
                refine ⟨16858346117714233297010653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22477794823618977729347537 16858346117714233297010653)
                ·
                  refine ⟨6321879794142837486378995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16858346117714233297010653 6321879794142837486378995)
                  ·
                    refine ⟨9482819691214256229568493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6321879794142837486378995 9482819691214256229568493)
                    ·
                      refine ⟨3556057384205346086088185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9482819691214256229568493 3556057384205346086088185)
                      ·
                        rfl

theorem cell23_6925397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 2, 3, 1, 3].length) (baseStart_6925397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6925397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6925397 prefixEnd_6925397 := by exact prefixLift 6925397
  have htrace : WordTrace (prefixWord ++ tailWord_6925397) baseStart_6925397 baseEnd_6925397 := by
    simpa [prefixWord, tailWord_6925397, baseEnd_6925397] using wordTrace_append hprefix tailTrace_6925397
  have hstable : (prefixWord ++ tailWord_6925397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6925397).length < 2 ^ (prefixWord ++ tailWord_6925397).sum := by decide
  have hdescent : baseEnd_6925397 < baseStart_6925397 := by decide
  rcases family_descends (prefixWord ++ tailWord_6925397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6925398 : List Nat := [5, 2, 2, 1, 3, 1, 1, 1, 2, 1, 4]
def baseStart_6925398 : Nat := 118140960795 + 6925398 * 2 ^ 59
def prefixEnd_6925398 : Nat := 4983230072969 + 3 ^ 40 * 6925398 * 2
def baseEnd_6925398 : Nat := 3556057897686000582175681

theorem tailTrace_6925398 : CollatzResearch.WordTrace tailWord_6925398 prefixEnd_6925398 3556057897686000582175681 := by
  unfold tailWord_6925398
  simp only [CollatzResearch.WordTrace]
  refine ⟨15786876010279580291179553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 168393344109648856439248565 15786876010279580291179553)
  ·
    refine ⟨11840157007709685218384665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15786876010279580291179553 11840157007709685218384665)
    ·
      refine ⟨8880117755782263913788499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11840157007709685218384665 8880117755782263913788499)
      ·
        refine ⟨13320176633673395870682749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8880117755782263913788499 13320176633673395870682749)
        ·
          refine ⟨4995066237627523451506031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13320176633673395870682749 4995066237627523451506031)
          ·
            refine ⟨7492599356441285177259047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4995066237627523451506031 7492599356441285177259047)
            ·
              refine ⟨11238899034661927765888571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7492599356441285177259047 11238899034661927765888571)
              ·
                refine ⟨16858348551992891648832857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11238899034661927765888571 16858348551992891648832857)
                ·
                  refine ⟨12643761413994668736624643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16858348551992891648832857 12643761413994668736624643)
                  ·
                    refine ⟨18965642120992003104936965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12643761413994668736624643 18965642120992003104936965)
                    ·
                      refine ⟨3556057897686000582175681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18965642120992003104936965 3556057897686000582175681)
                      ·
                        rfl

theorem cell23_6925398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_6925398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6925398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6925398 prefixEnd_6925398 := by exact prefixLift 6925398
  have htrace : WordTrace (prefixWord ++ tailWord_6925398) baseStart_6925398 baseEnd_6925398 := by
    simpa [prefixWord, tailWord_6925398, baseEnd_6925398] using wordTrace_append hprefix tailTrace_6925398
  have hstable : (prefixWord ++ tailWord_6925398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6925398).length < 2 ^ (prefixWord ++ tailWord_6925398).sum := by decide
  have hdescent : baseEnd_6925398 < baseStart_6925398 := by decide
  rcases family_descends (prefixWord ++ tailWord_6925398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6925400 : List Nat := [2, 1, 2, 2, 1, 3, 2, 4, 1, 5]
def baseStart_6925400 : Nat := 118140960795 + 6925400 * 2 ^ 59
def prefixEnd_6925400 : Nat := 4983230072969 + 3 ^ 40 * 6925400 * 2
def baseEnd_6925400 : Nat := 1185352974882436524783557

theorem tailTrace_6925400 : CollatzResearch.WordTrace tailWord_6925400 prefixEnd_6925400 1185352974882436524783557 := by
  unfold tailWord_6925400
  simp only [CollatzResearch.WordTrace]
  refine ⟨126295044555233019500222827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168393392740310692666963769 126295044555233019500222827)
  ·
    refine ⟨189442566832849529250334241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126295044555233019500222827 189442566832849529250334241)
    ·
      refine ⟨142081925124637146937750681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189442566832849529250334241 142081925124637146937750681)
      ·
        refine ⟨106561443843477860203313011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142081925124637146937750681 106561443843477860203313011)
        ·
          refine ⟨159842165765216790304969517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106561443843477860203313011 159842165765216790304969517)
          ·
            refine ⟨59940812161956296364363569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159842165765216790304969517 59940812161956296364363569)
            ·
              refine ⟨44955609121467222273272677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59940812161956296364363569 44955609121467222273272677)
              ·
                refine ⟨8429176710275104176238627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44955609121467222273272677 8429176710275104176238627)
                ·
                  refine ⟨12643765065412656264357941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8429176710275104176238627 12643765065412656264357941)
                  ·
                    refine ⟨1185352974882436524783557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12643765065412656264357941 1185352974882436524783557)
                    ·
                      rfl

theorem cell23_6925400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 4, 1, 5].length) (baseStart_6925400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6925400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6925400 prefixEnd_6925400 := by exact prefixLift 6925400
  have htrace : WordTrace (prefixWord ++ tailWord_6925400) baseStart_6925400 baseEnd_6925400 := by
    simpa [prefixWord, tailWord_6925400, baseEnd_6925400] using wordTrace_append hprefix tailTrace_6925400
  have hstable : (prefixWord ++ tailWord_6925400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6925400).length < 2 ^ (prefixWord ++ tailWord_6925400).sum := by decide
  have hdescent : baseEnd_6925400 < baseStart_6925400 := by decide
  rcases family_descends (prefixWord ++ tailWord_6925400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6925417 : List Nat := [1, 2, 1, 1, 1, 6, 4, 1, 1, 5]
def baseStart_6925417 : Nat := 118140960795 + 6925417 * 2 ^ 59
def prefixEnd_6925417 : Nat := 4983230072969 + 3 ^ 40 * 6925417 * 2
def baseEnd_6925417 : Nat := 1185355884606145335946031

theorem tailTrace_6925417 : CollatzResearch.WordTrace tailWord_6925417 prefixEnd_6925417 1185355884606145335946031 := by
  unfold tailWord_6925417
  simp only [CollatzResearch.WordTrace]
  refine ⟨252590709151404450903814505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168393806100936300602543003 252590709151404450903814505)
  ·
    refine ⟨189443031863553338177860879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252590709151404450903814505 189443031863553338177860879)
    ·
      refine ⟨284164547795330007266791319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189443031863553338177860879 284164547795330007266791319)
      ·
        refine ⟨426246821692995010900186979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284164547795330007266791319 426246821692995010900186979)
        ·
          refine ⟨639370232539492516350280469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426246821692995010900186979 639370232539492516350280469)
          ·
            refine ⟨29970479650288711703919397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 639370232539492516350280469 29970479650288711703919397)
            ·
              refine ⟨5619464934429133444484887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29970479650288711703919397 5619464934429133444484887)
              ·
                refine ⟨8429197401643700166727331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5619464934429133444484887 8429197401643700166727331)
                ·
                  refine ⟨12643796102465550250090997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8429197401643700166727331 12643796102465550250090997)
                  ·
                    refine ⟨1185355884606145335946031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12643796102465550250090997 1185355884606145335946031)
                    ·
                      rfl

theorem cell23_6925417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 4, 1, 1, 5].length) (baseStart_6925417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6925417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6925417 prefixEnd_6925417 := by exact prefixLift 6925417
  have htrace : WordTrace (prefixWord ++ tailWord_6925417) baseStart_6925417 baseEnd_6925417 := by
    simpa [prefixWord, tailWord_6925417, baseEnd_6925417] using wordTrace_append hprefix tailTrace_6925417
  have hstable : (prefixWord ++ tailWord_6925417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6925417).length < 2 ^ (prefixWord ++ tailWord_6925417).sum := by decide
  have hdescent : baseEnd_6925417 < baseStart_6925417 := by decide
  rcases family_descends (prefixWord ++ tailWord_6925417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6925438 : List Nat := [4, 2, 4, 1, 1, 1, 3, 1, 6]
def baseStart_6925438 : Nat := 118140960795 + 6925438 * 2 ^ 59
def prefixEnd_6925438 : Nat := 4983230072969 + 3 ^ 40 * 6925438 * 2
def baseEnd_6925438 : Nat := 395119826323575602852833

theorem tailTrace_6925438 : CollatzResearch.WordTrace tailWord_6925438 prefixEnd_6925438 395119826323575602852833 := by
  unfold tailWord_6925438
  simp only [CollatzResearch.WordTrace]
  refine ⟨31573934385541046436291121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168394316722885580993552645 31573934385541046436291121)
  ·
    refine ⟨23680450789155784827218341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31573934385541046436291121 23680450789155784827218341)
    ·
      refine ⟨4440084522966709655103439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23680450789155784827218341 4440084522966709655103439)
      ·
        refine ⟨6660126784450064482655159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4440084522966709655103439 6660126784450064482655159)
        ·
          refine ⟨9990190176675096723982739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6660126784450064482655159 9990190176675096723982739)
          ·
            refine ⟨14985285265012645085974109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9990190176675096723982739 14985285265012645085974109)
            ·
              refine ⟨5619481974379741907240291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14985285265012645085974109 5619481974379741907240291)
              ·
                refine ⟨8429222961569612860860437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5619481974379741907240291 8429222961569612860860437)
                ·
                  refine ⟨395119826323575602852833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8429222961569612860860437 395119826323575602852833)
                  ·
                    rfl

theorem cell23_6925438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 3, 1, 6].length) (baseStart_6925438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6925438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6925438 prefixEnd_6925438 := by exact prefixLift 6925438
  have htrace : WordTrace (prefixWord ++ tailWord_6925438) baseStart_6925438 baseEnd_6925438 := by
    simpa [prefixWord, tailWord_6925438, baseEnd_6925438] using wordTrace_append hprefix tailTrace_6925438
  have hstable : (prefixWord ++ tailWord_6925438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6925438).length < 2 ^ (prefixWord ++ tailWord_6925438).sum := by decide
  have hdescent : baseEnd_6925438 < baseStart_6925438 := by decide
  rcases family_descends (prefixWord ++ tailWord_6925438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6925440 : List Nat := [2, 1, 1, 2, 1, 3, 2, 1, 5, 2, 3]
def baseStart_6925440 : Nat := 118140960795 + 6925440 * 2 ^ 59
def prefixEnd_6925440 : Nat := 4983230072969 + 3 ^ 40 * 6925440 * 2
def baseEnd_6925440 : Nat := 3556079463873489417850487

theorem tailTrace_6925440 : CollatzResearch.WordTrace tailWord_6925440 prefixEnd_6925440 3556079463873489417850487 := by
  unfold tailWord_6925440
  simp only [CollatzResearch.WordTrace]
  refine ⟨126295774015160562915950887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168394365353547417221267849 126295774015160562915950887)
  ·
    refine ⟨189443661022740844373926331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126295774015160562915950887 189443661022740844373926331)
    ·
      refine ⟨284165491534111266560889497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189443661022740844373926331 284165491534111266560889497)
      ·
        refine ⟨213124118650583449920667123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 284165491534111266560889497 213124118650583449920667123)
        ·
          refine ⟨319686177975875174881000685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213124118650583449920667123 319686177975875174881000685)
          ·
            refine ⟨119882316740953190580375257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 319686177975875174881000685 119882316740953190580375257)
            ·
              refine ⟨89911737555714892935281443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119882316740953190580375257 89911737555714892935281443)
              ·
                refine ⟨134867606333572339402922165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89911737555714892935281443 134867606333572339402922165)
                ·
                  refine ⟨12643838093772406819023953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 134867606333572339402922165 12643838093772406819023953)
                  ·
                    refine ⟨9482878570329305114267965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12643838093772406819023953 9482878570329305114267965)
                    ·
                      refine ⟨3556079463873489417850487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9482878570329305114267965 3556079463873489417850487)
                      ·
                        rfl

theorem cell23_6925440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 5, 2, 3].length) (baseStart_6925440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6925440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6925440 prefixEnd_6925440 := by exact prefixLift 6925440
  have htrace : WordTrace (prefixWord ++ tailWord_6925440) baseStart_6925440 baseEnd_6925440 := by
    simpa [prefixWord, tailWord_6925440, baseEnd_6925440] using wordTrace_append hprefix tailTrace_6925440
  have hstable : (prefixWord ++ tailWord_6925440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6925440).length < 2 ^ (prefixWord ++ tailWord_6925440).sum := by decide
  have hdescent : baseEnd_6925440 < baseStart_6925440 := by decide
  rcases family_descends (prefixWord ++ tailWord_6925440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6925443 : List Nat := [1, 1, 1, 3, 3, 2, 2, 10]
def baseStart_6925443 : Nat := 118140960795 + 6925443 * 2 ^ 59
def prefixEnd_6925443 : Nat := 4983230072969 + 3 ^ 40 * 6925443 * 2
def baseEnd_6925443 : Nat := 131706703863535292818999

theorem tailTrace_6925443 : CollatzResearch.WordTrace tailWord_6925443 prefixEnd_6925443 131706703863535292818999 := by
  unfold tailWord_6925443
  simp only [CollatzResearch.WordTrace]
  refine ⟨252591657449310257344260983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168394438299540171562840655 252591657449310257344260983)
  ·
    refine ⟨378887486173965386016391475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252591657449310257344260983 378887486173965386016391475)
    ·
      refine ⟨568331229260948079024587213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378887486173965386016391475 568331229260948079024587213)
      ·
        refine ⟨213124210972855529634220205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 568331229260948079024587213 213124210972855529634220205)
        ·
          refine ⟨79921579114820823612832577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 213124210972855529634220205 79921579114820823612832577)
          ·
            refine ⟨59941184336115617709624433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79921579114820823612832577 59941184336115617709624433)
            ·
              refine ⟨44955888252086713282218325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59941184336115617709624433 44955888252086713282218325)
              ·
                refine ⟨131706703863535292818999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 44955888252086713282218325 131706703863535292818999)
                ·
                  rfl

theorem cell23_6925443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 10].length) (baseStart_6925443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6925443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6925443 prefixEnd_6925443 := by exact prefixLift 6925443
  have htrace : WordTrace (prefixWord ++ tailWord_6925443) baseStart_6925443 baseEnd_6925443 := by
    simpa [prefixWord, tailWord_6925443, baseEnd_6925443] using wordTrace_append hprefix tailTrace_6925443
  have hstable : (prefixWord ++ tailWord_6925443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6925443).length < 2 ^ (prefixWord ++ tailWord_6925443).sum := by decide
  have hdescent : baseEnd_6925443 < baseStart_6925443 := by decide
  rcases family_descends (prefixWord ++ tailWord_6925443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6925450 : List Nat := [3, 1, 2, 3, 1, 1, 3, 1, 1, 1, 6]
def baseStart_6925450 : Nat := 118140960795 + 6925450 * 2 ^ 59
def prefixEnd_6925450 : Nat := 4983230072969 + 3 ^ 40 * 6925450 * 2
def baseEnd_6925450 : Nat := 3556084598680034378725441

theorem tailTrace_6925450 : CollatzResearch.WordTrace tailWord_6925450 prefixEnd_6925450 3556084598680034378725441 := by
  unfold tailWord_6925450
  simp only [CollatzResearch.WordTrace]
  refine ⟨63147978190071224384941451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168394608506856598359843869 63147978190071224384941451)
  ·
    refine ⟨94721967285106836577412177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63147978190071224384941451 94721967285106836577412177)
    ·
      refine ⟨71041475463830127433059133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94721967285106836577412177 71041475463830127433059133)
      ·
        refine ⟨26640553298936297787397175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71041475463830127433059133 26640553298936297787397175)
        ·
          refine ⟨39960829948404446681095763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26640553298936297787397175 39960829948404446681095763)
          ·
            refine ⟨59941244922606670021643645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39960829948404446681095763 59941244922606670021643645)
            ·
              refine ⟨22477966845977501258116367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59941244922606670021643645 22477966845977501258116367)
              ·
                refine ⟨33716950268966251887174551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22477966845977501258116367 33716950268966251887174551)
                ·
                  refine ⟨50575425403449377830761827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33716950268966251887174551 50575425403449377830761827)
                  ·
                    refine ⟨75863138105174066746142741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50575425403449377830761827 75863138105174066746142741)
                    ·
                      refine ⟨3556084598680034378725441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75863138105174066746142741 3556084598680034378725441)
                      ·
                        rfl

theorem cell23_6925450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_6925450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6925450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6925450 prefixEnd_6925450 := by exact prefixLift 6925450
  have htrace : WordTrace (prefixWord ++ tailWord_6925450) baseStart_6925450 baseEnd_6925450 := by
    simpa [prefixWord, tailWord_6925450, baseEnd_6925450] using wordTrace_append hprefix tailTrace_6925450
  have hstable : (prefixWord ++ tailWord_6925450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6925450).length < 2 ^ (prefixWord ++ tailWord_6925450).sum := by decide
  have hdescent : baseEnd_6925450 < baseStart_6925450 := by decide
  rcases family_descends (prefixWord ++ tailWord_6925450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6925454 : List Nat := [4, 1, 1, 3, 2, 2, 2, 2, 1, 1, 4]
def baseStart_6925454 : Nat := 118140960795 + 6925454 * 2 ^ 59
def prefixEnd_6925454 : Nat := 4983230072969 + 3 ^ 40 * 6925454 * 2
def baseEnd_6925454 : Nat := 3556086652602652363075423

theorem tailTrace_6925454 : CollatzResearch.WordTrace tailWord_6925454 prefixEnd_6925454 3556086652602652363075423 := by
  unfold tailWord_6925454
  simp only [CollatzResearch.WordTrace]
  refine ⟨31574007331533800777863927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168394705768180270815274277 31574007331533800777863927)
  ·
    refine ⟨47361010997300701166795891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31574007331533800777863927 47361010997300701166795891)
    ·
      refine ⟨71041516495951051750193837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47361010997300701166795891 71041516495951051750193837)
      ·
        refine ⟨26640568685981644406322689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71041516495951051750193837 26640568685981644406322689)
        ·
          refine ⟨19980426514486233304742017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26640568685981644406322689 19980426514486233304742017)
          ·
            refine ⟨14985319885864674978556513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19980426514486233304742017 14985319885864674978556513)
            ·
              refine ⟨11238989914398506233917385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14985319885864674978556513 11238989914398506233917385)
              ·
                refine ⟨8429242435798879675438039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11238989914398506233917385 8429242435798879675438039)
                ·
                  refine ⟨12643863653698319513157059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8429242435798879675438039 12643863653698319513157059)
                  ·
                    refine ⟨18965795480547479269735589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12643863653698319513157059 18965795480547479269735589)
                    ·
                      refine ⟨3556086652602652363075423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18965795480547479269735589 3556086652602652363075423)
                      ·
                        rfl

theorem cell23_6925454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_6925454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6925454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6925454 prefixEnd_6925454 := by exact prefixLift 6925454
  have htrace : WordTrace (prefixWord ++ tailWord_6925454) baseStart_6925454 baseEnd_6925454 := by
    simpa [prefixWord, tailWord_6925454, baseEnd_6925454] using wordTrace_append hprefix tailTrace_6925454
  have hstable : (prefixWord ++ tailWord_6925454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6925454).length < 2 ^ (prefixWord ++ tailWord_6925454).sum := by decide
  have hdescent : baseEnd_6925454 < baseStart_6925454 := by decide
  rcases family_descends (prefixWord ++ tailWord_6925454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6925474 : List Nat := [3, 3, 1, 3, 2, 1, 2, 1, 1, 1, 5]
def baseStart_6925474 : Nat := 118140960795 + 6925474 * 2 ^ 59
def prefixEnd_6925474 : Nat := 4983230072969 + 3 ^ 40 * 6925474 * 2
def baseEnd_6925474 : Nat := 3556096922215742284825331

theorem tailTrace_6925474 : CollatzResearch.WordTrace tailWord_6925474 prefixEnd_6925474 3556096922215742284825331 := by
  unfold tailWord_6925474
  simp only [CollatzResearch.WordTrace]
  refine ⟨63148197028049487409659869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168395192074798633092426317 63148197028049487409659869)
  ·
    refine ⟨23680573885518557778622451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63148197028049487409659869 23680573885518557778622451)
    ·
      refine ⟨35520860828277836667933677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23680573885518557778622451 35520860828277836667933677)
      ·
        refine ⟨13320322810604188750475129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35520860828277836667933677 13320322810604188750475129)
        ·
          refine ⟨9990242107953141562856347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13320322810604188750475129 9990242107953141562856347)
          ·
            refine ⟨14985363161929712344284521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9990242107953141562856347 14985363161929712344284521)
            ·
              refine ⟨11239022371447284258213391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14985363161929712344284521 11239022371447284258213391)
              ·
                refine ⟨16858533557170926387320087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11239022371447284258213391 16858533557170926387320087)
                ·
                  refine ⟨25287800335756389580980131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16858533557170926387320087 25287800335756389580980131)
                  ·
                    refine ⟨37931700503634584371470197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25287800335756389580980131 37931700503634584371470197)
                    ·
                      refine ⟨3556096922215742284825331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37931700503634584371470197 3556096922215742284825331)
                      ·
                        rfl

theorem cell23_6925474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_6925474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6925474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6925474 prefixEnd_6925474 := by exact prefixLift 6925474
  have htrace : WordTrace (prefixWord ++ tailWord_6925474) baseStart_6925474 baseEnd_6925474 := by
    simpa [prefixWord, tailWord_6925474, baseEnd_6925474] using wordTrace_append hprefix tailTrace_6925474
  have hstable : (prefixWord ++ tailWord_6925474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6925474).length < 2 ^ (prefixWord ++ tailWord_6925474).sum := by decide
  have hdescent : baseEnd_6925474 < baseStart_6925474 := by decide
  rcases family_descends (prefixWord ++ tailWord_6925474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6925487 : List Nat := [1, 1, 2, 1, 2, 3, 4, 1, 4, 1, 3]
def baseStart_6925487 : Nat := 118140960795 + 6925487 * 2 ^ 59
def prefixEnd_6925487 : Nat := 4983230072969 + 3 ^ 40 * 6925487 * 2
def baseEnd_6925487 : Nat := 3556103597464250733962771

theorem tailTrace_6925487 : CollatzResearch.WordTrace tailWord_6925487 prefixEnd_6925487 3556103597464250733962771 := by
  unfold tailWord_6925487
  simp only [CollatzResearch.WordTrace]
  refine ⟨252593262261150852858862715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168395508174100568572575143 252593262261150852858862715)
  ·
    refine ⟨378889893391726279288294073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252593262261150852858862715 378889893391726279288294073)
    ·
      refine ⟨284167420043794709466220555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 378889893391726279288294073 284167420043794709466220555)
      ·
        refine ⟨426251130065692064199330833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284167420043794709466220555 426251130065692064199330833)
        ·
          refine ⟨319688347549269048149498125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 426251130065692064199330833 319688347549269048149498125)
          ·
            refine ⟨119883130330975893056061797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 319688347549269048149498125 119883130330975893056061797)
            ·
              refine ⟨22478086937057979948011587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119883130330975893056061797 22478086937057979948011587)
              ·
                refine ⟨33717130405586969922017381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22478086937057979948011587 33717130405586969922017381)
                ·
                  refine ⟨6321961951047556860378259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33717130405586969922017381 6321961951047556860378259)
                  ·
                    refine ⟨9482942926571335290567389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6321961951047556860378259 9482942926571335290567389)
                    ·
                      refine ⟨3556103597464250733962771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9482942926571335290567389 3556103597464250733962771)
                      ·
                        rfl

theorem cell23_6925487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 4, 1, 3].length) (baseStart_6925487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6925487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6925487 prefixEnd_6925487 := by exact prefixLift 6925487
  have htrace : WordTrace (prefixWord ++ tailWord_6925487) baseStart_6925487 baseEnd_6925487 := by
    simpa [prefixWord, tailWord_6925487, baseEnd_6925487] using wordTrace_append hprefix tailTrace_6925487
  have hstable : (prefixWord ++ tailWord_6925487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6925487).length < 2 ^ (prefixWord ++ tailWord_6925487).sum := by decide
  have hdescent : baseEnd_6925487 < baseStart_6925487 := by decide
  rcases family_descends (prefixWord ++ tailWord_6925487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6925508 : List Nat := [2, 3, 3, 1, 4, 1, 1, 2, 1, 2, 3]
def baseStart_6925508 : Nat := 118140960795 + 6925508 * 2 ^ 59
def prefixEnd_6925508 : Nat := 4983230072969 + 3 ^ 40 * 6925508 * 2
def baseEnd_6925508 : Nat := 3556114380557995151800175

theorem tailTrace_6925508 : CollatzResearch.WordTrace tailWord_6925508 prefixEnd_6925508 3556114380557995151800175 := by
  unfold tailWord_6925508
  simp only [CollatzResearch.WordTrace]
  refine ⟨126297014097037386722688589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168396018796049848963584785 126297014097037386722688589)
  ·
    refine ⟨47361380286389020021008221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126297014097037386722688589 47361380286389020021008221)
    ·
      refine ⟨17760517607395882507878083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47361380286389020021008221 17760517607395882507878083)
      ·
        refine ⟨26640776411093823761817125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17760517607395882507878083 26640776411093823761817125)
        ·
          refine ⟨4995145577080091955340711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26640776411093823761817125 4995145577080091955340711)
          ·
            refine ⟨7492718365620137933011067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4995145577080091955340711 7492718365620137933011067)
            ·
              refine ⟨11239077548430206899516601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7492718365620137933011067 11239077548430206899516601)
              ·
                refine ⟨8429308161322655174637451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11239077548430206899516601 8429308161322655174637451)
                ·
                  refine ⟨12643962241983982761956177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8429308161322655174637451 12643962241983982761956177)
                  ·
                    refine ⟨9482971681487987071467133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12643962241983982761956177 9482971681487987071467133)
                    ·
                      refine ⟨3556114380557995151800175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9482971681487987071467133 3556114380557995151800175)
                      ·
                        rfl

theorem cell23_6925508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 2, 1, 2, 3].length) (baseStart_6925508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6925508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6925508 prefixEnd_6925508 := by exact prefixLift 6925508
  have htrace : WordTrace (prefixWord ++ tailWord_6925508) baseStart_6925508 baseEnd_6925508 := by
    simpa [prefixWord, tailWord_6925508, baseEnd_6925508] using wordTrace_append hprefix tailTrace_6925508
  have hstable : (prefixWord ++ tailWord_6925508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6925508).length < 2 ^ (prefixWord ++ tailWord_6925508).sum := by decide
  have hdescent : baseEnd_6925508 < baseStart_6925508 := by decide
  rcases family_descends (prefixWord ++ tailWord_6925508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6925514 : List Nat := [3, 1, 2, 1, 3, 3, 1, 1, 3, 3, 2]
def baseStart_6925514 : Nat := 118140960795 + 6925514 * 2 ^ 59
def prefixEnd_6925514 : Nat := 4983230072969 + 3 ^ 40 * 6925514 * 2
def baseEnd_6925514 : Nat := 3556117461441922128325147

theorem tailTrace_6925514 : CollatzResearch.WordTrace tailWord_6925514 prefixEnd_6925514 3556117461441922128325147 := by
  unfold tailWord_6925514
  simp only [CollatzResearch.WordTrace]
  refine ⟨63148561758013259117523899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168396164688035357646730397 63148561758013259117523899)
  ·
    refine ⟨94722842637019888676285849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63148561758013259117523899 94722842637019888676285849)
    ·
      refine ⟨71042131977764916507214387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94722842637019888676285849 71042131977764916507214387)
      ·
        refine ⟨106563197966647374760821581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71042131977764916507214387 106563197966647374760821581)
        ·
          refine ⟨39961199237492765535308093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106563197966647374760821581 39961199237492765535308093)
          ·
            refine ⟨14985449714059787075740535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39961199237492765535308093 14985449714059787075740535)
            ·
              refine ⟨22478174571089680613610803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14985449714059787075740535 22478174571089680613610803)
              ·
                refine ⟨33717261856634520920416205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22478174571089680613610803 33717261856634520920416205)
                ·
                  refine ⟨12643973196237945345156077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33717261856634520920416205 12643973196237945345156077)
                  ·
                    refine ⟨4741489948589229504433529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12643973196237945345156077 4741489948589229504433529)
                    ·
                      refine ⟨3556117461441922128325147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4741489948589229504433529 3556117461441922128325147)
                      ·
                        rfl

theorem cell23_6925514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 3, 3, 2].length) (baseStart_6925514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6925514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6925514 prefixEnd_6925514 := by exact prefixLift 6925514
  have htrace : WordTrace (prefixWord ++ tailWord_6925514) baseStart_6925514 baseEnd_6925514 := by
    simpa [prefixWord, tailWord_6925514, baseEnd_6925514] using wordTrace_append hprefix tailTrace_6925514
  have hstable : (prefixWord ++ tailWord_6925514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6925514).length < 2 ^ (prefixWord ++ tailWord_6925514).sum := by decide
  have hdescent : baseEnd_6925514 < baseStart_6925514 := by decide
  rcases family_descends (prefixWord ++ tailWord_6925514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6925527 : List Nat := [1, 1, 3, 2, 1, 2, 3, 1, 3, 4, 2]
def baseStart_6925527 : Nat := 118140960795 + 6925527 * 2 ^ 59
def prefixEnd_6925527 : Nat := 4983230072969 + 3 ^ 40 * 6925527 * 2
def baseEnd_6925527 : Nat := 3556124136690430577462587

theorem tailTrace_6925527 : CollatzResearch.WordTrace tailWord_6925527 prefixEnd_6925527 3556124136690430577462587 := by
  unfold tailWord_6925527
  simp only [CollatzResearch.WordTrace]
  refine ⟨252594721181005939690318835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168396480787337293126879223 252594721181005939690318835)
  ·
    refine ⟨378892081771508909535478253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252594721181005939690318835 378892081771508909535478253)
    ·
      refine ⟨142084530664315841075804345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 378892081771508909535478253 142084530664315841075804345)
      ·
        refine ⟨106563397998236880806853259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142084530664315841075804345 106563397998236880806853259)
        ·
          refine ⟨159845096997355321210279889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106563397998236880806853259 159845096997355321210279889)
          ·
            refine ⟨119883822748016490907709917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159845096997355321210279889 119883822748016490907709917)
            ·
              refine ⟨44956433530506184090391219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119883822748016490907709917 44956433530506184090391219)
              ·
                refine ⟨67434650295759276135586829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44956433530506184090391219 67434650295759276135586829)
                ·
                  refine ⟨25287993860909728550845061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67434650295759276135586829 25287993860909728550845061)
                  ·
                    refine ⟨4741498848920574103283449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25287993860909728550845061 4741498848920574103283449)
                    ·
                      refine ⟨3556124136690430577462587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4741498848920574103283449 3556124136690430577462587)
                      ·
                        rfl

theorem cell23_6925527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 3, 4, 2].length) (baseStart_6925527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6925527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6925527 prefixEnd_6925527 := by exact prefixLift 6925527
  have htrace : WordTrace (prefixWord ++ tailWord_6925527) baseStart_6925527 baseEnd_6925527 := by
    simpa [prefixWord, tailWord_6925527, baseEnd_6925527] using wordTrace_append hprefix tailTrace_6925527
  have hstable : (prefixWord ++ tailWord_6925527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6925527).length < 2 ^ (prefixWord ++ tailWord_6925527).sum := by decide
  have hdescent : baseEnd_6925527 < baseStart_6925527 := by decide
  rcases family_descends (prefixWord ++ tailWord_6925527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6925617 : List Nat := [1, 2, 2, 3, 3, 1, 1, 2, 1, 3, 4]
def baseStart_6925617 : Nat := 118140960795 + 6925617 * 2 ^ 59
def prefixEnd_6925617 : Nat := 4983230072969 + 3 ^ 40 * 6925617 * 2
def baseEnd_6925617 : Nat := 3556170349949335225337173

theorem tailTrace_6925617 : CollatzResearch.WordTrace tailWord_6925617 prefixEnd_6925617 3556170349949335225337173 := by
  unfold tailWord_6925617
  simp only [CollatzResearch.WordTrace]
  refine ⟨252598003750679885061095105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168398669167119923374063403 252598003750679885061095105)
  ·
    refine ⟨189448502813009913795821329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252598003750679885061095105 189448502813009913795821329)
    ·
      refine ⟨142086377109757435346865997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189448502813009913795821329 142086377109757435346865997)
      ·
        refine ⟨53282391416159038255074749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142086377109757435346865997 53282391416159038255074749)
        ·
          refine ⟨19980896781059639345653031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53282391416159038255074749 19980896781059639345653031)
          ·
            refine ⟨29971345171589459018479547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19980896781059639345653031 29971345171589459018479547)
            ·
              refine ⟨44957017757384188527719321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29971345171589459018479547 44957017757384188527719321)
              ·
                refine ⟨33717763318038141395789491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44957017757384188527719321 33717763318038141395789491)
                ·
                  refine ⟨50576644977057212093684237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33717763318038141395789491 50576644977057212093684237)
                  ·
                    refine ⟨18966241866396454535131589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50576644977057212093684237 18966241866396454535131589)
                    ·
                      refine ⟨3556170349949335225337173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18966241866396454535131589 3556170349949335225337173)
                      ·
                        rfl

theorem cell23_6925617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_6925617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6925617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6925617 prefixEnd_6925617 := by exact prefixLift 6925617
  have htrace : WordTrace (prefixWord ++ tailWord_6925617) baseStart_6925617 baseEnd_6925617 := by
    simpa [prefixWord, tailWord_6925617, baseEnd_6925617] using wordTrace_append hprefix tailTrace_6925617
  have hstable : (prefixWord ++ tailWord_6925617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6925617).length < 2 ^ (prefixWord ++ tailWord_6925617).sum := by decide
  have hdescent : baseEnd_6925617 < baseStart_6925617 := by decide
  rcases family_descends (prefixWord ++ tailWord_6925617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
