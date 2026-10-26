import V185TrunkScan22Chunk419

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3744148 : List Nat := [2, 4, 2, 1, 13]
def baseStart_3744148 : Nat := 118140960795 + 3744148 * 2 ^ 59
def prefixEnd_3744148 : Nat := 4983230072969 + 3 ^ 40 * 3744148 * 2
def baseEnd_3744148 : Nat := 5274478917888401200085

theorem tailTrace_3744148 : CollatzResearch.WordTrace tailWord_3744148 prefixEnd_3744148 5274478917888401200085 := by
  unfold tailWord_3744148
  simp only [CollatzResearch.WordTrace]
  refine ⟨68280148219799360207164549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91040197626399146942886065 68280148219799360207164549)
  ·
    refine ⟨12802527791212380038843353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68280148219799360207164549 12802527791212380038843353)
    ·
      refine ⟨9601895843409285029132515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12802527791212380038843353 9601895843409285029132515)
      ·
        refine ⟨14402843765113927543698773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9601895843409285029132515 14402843765113927543698773)
        ·
          refine ⟨5274478917888401200085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 14402843765113927543698773 5274478917888401200085)
          ·
            rfl

theorem cell22_3744148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 13].length) (baseStart_3744148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3744148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3744148 prefixEnd_3744148 := by exact prefixLift 3744148
  have htrace : WordTrace (prefixWord ++ tailWord_3744148) baseStart_3744148 baseEnd_3744148 := by
    simpa [prefixWord, tailWord_3744148, baseEnd_3744148] using wordTrace_append hprefix tailTrace_3744148
  have hstable : (prefixWord ++ tailWord_3744148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744148).length < 2 ^ (prefixWord ++ tailWord_3744148).sum := by decide
  have hdescent : baseEnd_3744148 < baseStart_3744148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744152 : List Nat := [2, 1, 2, 5, 1, 1, 1, 4, 2, 3]
def baseStart_3744152 : Nat := 118140960795 + 3744152 * 2 ^ 59
def prefixEnd_3744152 : Nat := 4983230072969 + 3 ^ 40 * 3744152 * 2
def baseEnd_3744152 : Nat := 1281699746328626814520643

theorem tailTrace_3744152 : CollatzResearch.WordTrace tailWord_3744152 prefixEnd_3744152 1281699746328626814520643 := by
  unfold tailWord_3744152
  simp only [CollatzResearch.WordTrace]
  refine ⟨68280221165792114548737355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91040294887722819398316473 68280221165792114548737355)
  ·
    refine ⟨102420331748688171823106033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68280221165792114548737355 102420331748688171823106033)
    ·
      refine ⟨76815248811516128867329525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102420331748688171823106033 76815248811516128867329525)
      ·
        refine ⟨7201429576079637081312143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76815248811516128867329525 7201429576079637081312143)
        ·
          refine ⟨10802144364119455621968215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7201429576079637081312143 10802144364119455621968215)
          ·
            refine ⟨16203216546179183432952323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10802144364119455621968215 16203216546179183432952323)
            ·
              refine ⟨24304824819268775149428485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16203216546179183432952323 24304824819268775149428485)
              ·
                refine ⟨4557154653612895340517841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24304824819268775149428485 4557154653612895340517841)
                ·
                  refine ⟨3417865990209671505388381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4557154653612895340517841 3417865990209671505388381)
                  ·
                    refine ⟨1281699746328626814520643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3417865990209671505388381 1281699746328626814520643)
                    ·
                      rfl

theorem cell22_3744152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 4, 2, 3].length) (baseStart_3744152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3744152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3744152 prefixEnd_3744152 := by exact prefixLift 3744152
  have htrace : WordTrace (prefixWord ++ tailWord_3744152) baseStart_3744152 baseEnd_3744152 := by
    simpa [prefixWord, tailWord_3744152, baseEnd_3744152] using wordTrace_append hprefix tailTrace_3744152
  have hstable : (prefixWord ++ tailWord_3744152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744152).length < 2 ^ (prefixWord ++ tailWord_3744152).sum := by decide
  have hdescent : baseEnd_3744152 < baseStart_3744152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744154 : List Nat := [3, 1, 1, 4, 1, 4, 2, 2, 4]
def baseStart_3744154 : Nat := 118140960795 + 3744154 * 2 ^ 59
def prefixEnd_3744154 : Nat := 4983230072969 + 3 ^ 40 * 3744154 * 2
def baseEnd_3744154 : Nat := 427233476989833158656879

theorem tailTrace_3744154 : CollatzResearch.WordTrace tailWord_3744154 prefixEnd_3744154 427233476989833158656879 := by
  unfold tailWord_3744154
  simp only [CollatzResearch.WordTrace]
  refine ⟨34140128819394245859761879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91040343518384655626031677 34140128819394245859761879)
  ·
    refine ⟨51210193229091368789642819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34140128819394245859761879 51210193229091368789642819)
    ·
      refine ⟨76815289843637053184464229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51210193229091368789642819 76815289843637053184464229)
      ·
        refine ⟨14402866845681947472087043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76815289843637053184464229 14402866845681947472087043)
        ·
          refine ⟨21604300268522921208130565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14402866845681947472087043 21604300268522921208130565)
          ·
            refine ⟨4050806300348047726524481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21604300268522921208130565 4050806300348047726524481)
            ·
              refine ⟨3038104725261035794893361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4050806300348047726524481 3038104725261035794893361)
              ·
                refine ⟨2278578543945776846170021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3038104725261035794893361 2278578543945776846170021)
                ·
                  refine ⟨427233476989833158656879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2278578543945776846170021 427233476989833158656879)
                  ·
                    rfl

theorem cell22_3744154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 2, 2, 4].length) (baseStart_3744154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3744154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3744154 prefixEnd_3744154 := by exact prefixLift 3744154
  have htrace : WordTrace (prefixWord ++ tailWord_3744154) baseStart_3744154 baseEnd_3744154 := by
    simpa [prefixWord, tailWord_3744154, baseEnd_3744154] using wordTrace_append hprefix tailTrace_3744154
  have hstable : (prefixWord ++ tailWord_3744154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744154).length < 2 ^ (prefixWord ++ tailWord_3744154).sum := by decide
  have hdescent : baseEnd_3744154 < baseStart_3744154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744178 : List Nat := [3, 2, 1, 1, 1, 1, 3, 2, 2, 6]
def baseStart_3744178 : Nat := 118140960795 + 3744178 * 2 ^ 59
def prefixEnd_3744178 : Nat := 4983230072969 + 3 ^ 40 * 3744178 * 2
def baseEnd_3744178 : Nat := 1281708646659971413370563

theorem tailTrace_3744178 : CollatzResearch.WordTrace tailWord_3744178 prefixEnd_3744178 1281708646659971413370563 := by
  unfold tailWord_3744178
  simp only [CollatzResearch.WordTrace]
  refine ⟨34140347657372508884480297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91040927086326690358614125 34140347657372508884480297)
  ·
    refine ⟨25605260743029381663360223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34140347657372508884480297 25605260743029381663360223)
    ·
      refine ⟨38407891114544072495040335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25605260743029381663360223 38407891114544072495040335)
      ·
        refine ⟨57611836671816108742560503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38407891114544072495040335 57611836671816108742560503)
        ·
          refine ⟨86417755007724163113840755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57611836671816108742560503 86417755007724163113840755)
          ·
            refine ⟨129626632511586244670761133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86417755007724163113840755 129626632511586244670761133)
            ·
              refine ⟨48609987191844841751535425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129626632511586244670761133 48609987191844841751535425)
              ·
                refine ⟨36457490393883631313651569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48609987191844841751535425 36457490393883631313651569)
                ·
                  refine ⟨27343117795412723485238677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36457490393883631313651569 27343117795412723485238677)
                  ·
                    refine ⟨1281708646659971413370563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27343117795412723485238677 1281708646659971413370563)
                    ·
                      rfl

theorem cell22_3744178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_3744178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3744178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3744178 prefixEnd_3744178 := by exact prefixLift 3744178
  have htrace : WordTrace (prefixWord ++ tailWord_3744178) baseStart_3744178 baseEnd_3744178 := by
    simpa [prefixWord, tailWord_3744178, baseEnd_3744178] using wordTrace_append hprefix tailTrace_3744178
  have hstable : (prefixWord ++ tailWord_3744178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744178).length < 2 ^ (prefixWord ++ tailWord_3744178).sum := by decide
  have hdescent : baseEnd_3744178 < baseStart_3744178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744214 : List Nat := [5, 2, 1, 1, 1, 1, 4, 1, 3, 3]
def baseStart_3744214 : Nat := 118140960795 + 3744214 * 2 ^ 59
def prefixEnd_3744214 : Nat := 4983230072969 + 3 ^ 40 * 3744214 * 2
def baseEnd_3744214 : Nat := 1281720970195679319470453

theorem tailTrace_3744214 : CollatzResearch.WordTrace tailWord_3744214 prefixEnd_3744214 1281720970195679319470453 := by
  unfold tailWord_3744214
  simp only [CollatzResearch.WordTrace]
  refine ⟨8535168978584975855389481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91041802438239742457487797 8535168978584975855389481)
  ·
    refine ⟨6401376733938731891542111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8535168978584975855389481 6401376733938731891542111)
    ·
      refine ⟨9602065100908097837313167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6401376733938731891542111 9602065100908097837313167)
      ·
        refine ⟨14403097651362146755969751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9602065100908097837313167 14403097651362146755969751)
        ·
          refine ⟨21604646477043220133954627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14403097651362146755969751 21604646477043220133954627)
          ·
            refine ⟨32406969715564830200931941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21604646477043220133954627 32406969715564830200931941)
            ·
              refine ⟨6076306821668405662674739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32406969715564830200931941 6076306821668405662674739)
              ·
                refine ⟨9114460232502608494012109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6076306821668405662674739 9114460232502608494012109)
                ·
                  refine ⟨3417922587188478185254541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9114460232502608494012109 3417922587188478185254541)
                  ·
                    refine ⟨1281720970195679319470453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3417922587188478185254541 1281720970195679319470453)
                    ·
                      rfl

theorem cell22_3744214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_3744214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3744214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3744214 prefixEnd_3744214 := by exact prefixLift 3744214
  have htrace : WordTrace (prefixWord ++ tailWord_3744214) baseStart_3744214 baseEnd_3744214 := by
    simpa [prefixWord, tailWord_3744214, baseEnd_3744214] using wordTrace_append hprefix tailTrace_3744214
  have hstable : (prefixWord ++ tailWord_3744214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744214).length < 2 ^ (prefixWord ++ tailWord_3744214).sum := by decide
  have hdescent : baseEnd_3744214 < baseStart_3744214 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744257 : List Nat := [1, 2, 4, 1, 3, 1, 2, 3, 1, 4]
def baseStart_3744257 : Nat := 118140960795 + 3744257 * 2 ^ 59
def prefixEnd_3744257 : Nat := 4983230072969 + 3 ^ 40 * 3744257 * 2
def baseEnd_3744257 : Nat := 1281735689974441540645321

theorem tailTrace_3744257 : CollatzResearch.WordTrace tailWord_3744257 prefixEnd_3744257 1281735689974441540645321 := by
  unfold tailWord_3744257
  simp only [CollatzResearch.WordTrace]
  refine ⟨136564271996203832030047025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91042847997469221353364683 136564271996203832030047025)
  ·
    refine ⟨102423203997152874022535269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136564271996203832030047025 102423203997152874022535269)
    ·
      refine ⟨19204350749466163879225363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102423203997152874022535269 19204350749466163879225363)
      ·
        refine ⟨28806526124199245818838045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19204350749466163879225363 28806526124199245818838045)
        ·
          refine ⟨10802447296574717182064267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28806526124199245818838045 10802447296574717182064267)
          ·
            refine ⟨16203670944862075773096401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10802447296574717182064267 16203670944862075773096401)
            ·
              refine ⟨12152753208646556829822301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16203670944862075773096401 12152753208646556829822301)
              ·
                refine ⟨4557282453242458811183363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12152753208646556829822301 4557282453242458811183363)
                ·
                  refine ⟨6835923679863688216775045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4557282453242458811183363 6835923679863688216775045)
                  ·
                    refine ⟨1281735689974441540645321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6835923679863688216775045 1281735689974441540645321)
                    ·
                      rfl

theorem cell22_3744257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_3744257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3744257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3744257 prefixEnd_3744257 := by exact prefixLift 3744257
  have htrace : WordTrace (prefixWord ++ tailWord_3744257) baseStart_3744257 baseEnd_3744257 := by
    simpa [prefixWord, tailWord_3744257, baseEnd_3744257] using wordTrace_append hprefix tailTrace_3744257
  have hstable : (prefixWord ++ tailWord_3744257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744257).length < 2 ^ (prefixWord ++ tailWord_3744257).sum := by decide
  have hdescent : baseEnd_3744257 < baseStart_3744257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744308 : List Nat := [2, 5, 1, 3, 1, 1, 3, 1, 1, 4]
def baseStart_3744308 : Nat := 118140960795 + 3744308 * 2 ^ 59
def prefixEnd_3744308 : Nat := 4983230072969 + 3 ^ 40 * 3744308 * 2
def baseEnd_3744308 : Nat := 1281753148316694407620165

theorem tailTrace_3744308 : CollatzResearch.WordTrace tailWord_3744308 prefixEnd_3744308 1281753148316694407620165 := by
  unfold tailWord_3744308
  simp only [CollatzResearch.WordTrace]
  refine ⟨68283066059509533870076789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91044088079346045160102385 68283066059509533870076789)
  ·
    refine ⟨6401537443079018800319699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68283066059509533870076789 6401537443079018800319699)
    ·
      refine ⟨9602306164618528200479549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6401537443079018800319699 9602306164618528200479549)
      ·
        refine ⟨3600864811731948075179831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9602306164618528200479549 3600864811731948075179831)
        ·
          refine ⟨5401297217597922112769747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3600864811731948075179831 5401297217597922112769747)
          ·
            refine ⟨8101945826396883169154621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5401297217597922112769747 8101945826396883169154621)
            ·
              refine ⟨3038229684898831188432983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8101945826396883169154621 3038229684898831188432983)
              ·
                refine ⟨4557344527348246782649475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3038229684898831188432983 4557344527348246782649475)
                ·
                  refine ⟨6836016791022370173974213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4557344527348246782649475 6836016791022370173974213)
                  ·
                    refine ⟨1281753148316694407620165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6836016791022370173974213 1281753148316694407620165)
                    ·
                      rfl

theorem cell22_3744308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_3744308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3744308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3744308 prefixEnd_3744308 := by exact prefixLift 3744308
  have htrace : WordTrace (prefixWord ++ tailWord_3744308) baseStart_3744308 baseEnd_3744308 := by
    simpa [prefixWord, tailWord_3744308, baseEnd_3744308] using wordTrace_append hprefix tailTrace_3744308
  have hstable : (prefixWord ++ tailWord_3744308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744308).length < 2 ^ (prefixWord ++ tailWord_3744308).sum := by decide
  have hdescent : baseEnd_3744308 < baseStart_3744308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744330 : List Nat := [3, 1, 2, 1, 1, 4, 1, 1, 2, 6]
def baseStart_3744330 : Nat := 118140960795 + 3744330 * 2 ^ 59
def prefixEnd_3744330 : Nat := 4983230072969 + 3 ^ 40 * 3744330 * 2
def baseEnd_3744330 : Nat := 1281760679366293683570097

theorem tailTrace_3744330 : CollatzResearch.WordTrace tailWord_3744330 prefixEnd_3744330 1281760679366293683570097 := by
  unfold tailWord_3744330
  simp only [CollatzResearch.WordTrace]
  refine ⟨34141733631234841374363611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91044623016626243664969629 34141733631234841374363611)
  ·
    refine ⟨51212600446852262061545417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34141733631234841374363611 51212600446852262061545417)
    ·
      refine ⟨38409450335139196546159063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51212600446852262061545417 38409450335139196546159063)
      ·
        refine ⟨57614175502708794819238595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38409450335139196546159063 57614175502708794819238595)
        ·
          refine ⟨86421263254063192228857893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57614175502708794819238595 86421263254063192228857893)
          ·
            refine ⟨16203986860136848542910855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86421263254063192228857893 16203986860136848542910855)
            ·
              refine ⟨24305980290205272814366283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16203986860136848542910855 24305980290205272814366283)
              ·
                refine ⟨36458970435307909221549425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24305980290205272814366283 36458970435307909221549425)
                ·
                  refine ⟨27344227826480931916162069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36458970435307909221549425 27344227826480931916162069)
                  ·
                    refine ⟨1281760679366293683570097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27344227826480931916162069 1281760679366293683570097)
                    ·
                      rfl

theorem cell22_3744330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_3744330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3744330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3744330 prefixEnd_3744330 := by exact prefixLift 3744330
  have htrace : WordTrace (prefixWord ++ tailWord_3744330) baseStart_3744330 baseEnd_3744330 := by
    simpa [prefixWord, tailWord_3744330, baseEnd_3744330] using wordTrace_append hprefix tailTrace_3744330
  have hstable : (prefixWord ++ tailWord_3744330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744330).length < 2 ^ (prefixWord ++ tailWord_3744330).sum := by decide
  have hdescent : baseEnd_3744330 < baseStart_3744330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744332 : List Nat := [2, 2, 1, 3, 1, 2, 2, 3, 3, 3]
def baseStart_3744332 : Nat := 118140960795 + 3744332 * 2 ^ 59
def prefixEnd_3744332 : Nat := 4983230072969 + 3 ^ 40 * 3744332 * 2
def baseEnd_3744332 : Nat := 1281761364007166345020091

theorem tailTrace_3744332 : CollatzResearch.WordTrace tailWord_3744332 prefixEnd_3744332 1281761364007166345020091 := by
  unfold tailWord_3744332
  simp only [CollatzResearch.WordTrace]
  refine ⟨68283503735466059919513625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91044671647288079892684833 68283503735466059919513625)
  ·
    refine ⟨51212627801599544939635219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68283503735466059919513625 51212627801599544939635219)
    ·
      refine ⟨76818941702399317409452829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51212627801599544939635219 76818941702399317409452829)
      ·
        refine ⟨28807103138399744028544811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76818941702399317409452829 28807103138399744028544811)
        ·
          refine ⟨43210654707599616042817217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28807103138399744028544811 43210654707599616042817217)
          ·
            refine ⟨32407991030699712032112913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43210654707599616042817217 32407991030699712032112913)
            ·
              refine ⟨24305993273024784024084685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32407991030699712032112913 24305993273024784024084685)
              ·
                refine ⟨9114747477384294009031757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24305993273024784024084685 9114747477384294009031757)
                ·
                  refine ⟨3418030304019110253386909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9114747477384294009031757 3418030304019110253386909)
                  ·
                    refine ⟨1281761364007166345020091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3418030304019110253386909 1281761364007166345020091)
                    ·
                      rfl

theorem cell22_3744332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 3, 3, 3].length) (baseStart_3744332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3744332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3744332 prefixEnd_3744332 := by exact prefixLift 3744332
  have htrace : WordTrace (prefixWord ++ tailWord_3744332) baseStart_3744332 baseEnd_3744332 := by
    simpa [prefixWord, tailWord_3744332, baseEnd_3744332] using wordTrace_append hprefix tailTrace_3744332
  have hstable : (prefixWord ++ tailWord_3744332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744332).length < 2 ^ (prefixWord ++ tailWord_3744332).sum := by decide
  have hdescent : baseEnd_3744332 < baseStart_3744332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744366 : List Nat := [4, 1, 2, 2, 2, 1, 1, 5, 1, 3]
def baseStart_3744366 : Nat := 118140960795 + 3744366 * 2 ^ 59
def prefixEnd_3744366 : Nat := 4983230072969 + 3 ^ 40 * 3744366 * 2
def baseEnd_3744366 : Nat := 1281773002902001589669987

theorem tailTrace_3744366 : CollatzResearch.WordTrace tailWord_3744366 prefixEnd_3744366 1281773002902001589669987 := by
  unfold tailWord_3744366
  simp only [CollatzResearch.WordTrace]
  refine ⟨17071030944101117955720619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91045498368539295763843301 17071030944101117955720619)
  ·
    refine ⟨25606546416151676933580929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17071030944101117955720619 25606546416151676933580929)
    ·
      refine ⟨19204909812113757700185697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25606546416151676933580929 19204909812113757700185697)
      ·
        refine ⟨14403682359085318275139273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19204909812113757700185697 14403682359085318275139273)
        ·
          refine ⟨10802761769313988706354455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14403682359085318275139273 10802761769313988706354455)
          ·
            refine ⟨16204142653970983059531683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10802761769313988706354455 16204142653970983059531683)
            ·
              refine ⟨24306213980956474589297525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16204142653970983059531683 24306213980956474589297525)
              ·
                refine ⟨2278707560714669492746643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24306213980956474589297525 2278707560714669492746643)
                ·
                  refine ⟨3418061341072004239119965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2278707560714669492746643 3418061341072004239119965)
                  ·
                    refine ⟨1281773002902001589669987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3418061341072004239119965 1281773002902001589669987)
                    ·
                      rfl

theorem cell22_3744366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 5, 1, 3].length) (baseStart_3744366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3744366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3744366 prefixEnd_3744366 := by exact prefixLift 3744366
  have htrace : WordTrace (prefixWord ++ tailWord_3744366) baseStart_3744366 baseEnd_3744366 := by
    simpa [prefixWord, tailWord_3744366, baseEnd_3744366] using wordTrace_append hprefix tailTrace_3744366
  have hstable : (prefixWord ++ tailWord_3744366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744366).length < 2 ^ (prefixWord ++ tailWord_3744366).sum := by decide
  have hdescent : baseEnd_3744366 < baseStart_3744366 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744435 : List Nat := [1, 1, 1, 2, 3, 4, 10]
def baseStart_3744435 : Nat := 118140960795 + 3744435 * 2 ^ 59
def prefixEnd_3744435 : Nat := 4983230072969 + 3 ^ 40 * 3744435 * 2
def baseEnd_3744435 : Nat := 47473949000448459618325

theorem tailTrace_3744435 : CollatzResearch.WordTrace tailWord_3744435 prefixEnd_3744435 47473949000448459618325 := by
  unfold tailWord_3744435
  simp only [CollatzResearch.WordTrace]
  refine ⟨136570764189558968430026759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91047176126372645620017839 136570764189558968430026759)
  ·
    refine ⟨204856146284338452645040139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136570764189558968430026759 204856146284338452645040139)
    ·
      refine ⟨307284219426507678967560209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204856146284338452645040139 307284219426507678967560209)
      ·
        refine ⟨230463164569880759225670157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307284219426507678967560209 230463164569880759225670157)
        ·
          refine ⟨86423686713705284709626309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 230463164569880759225670157 86423686713705284709626309)
          ·
            refine ⟨16204441258819740883054933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86423686713705284709626309 16204441258819740883054933)
            ·
              refine ⟨47473949000448459618325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16204441258819740883054933 47473949000448459618325)
              ·
                rfl

theorem cell22_3744435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 10].length) (baseStart_3744435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3744435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3744435 prefixEnd_3744435 := by exact prefixLift 3744435
  have htrace : WordTrace (prefixWord ++ tailWord_3744435) baseStart_3744435 baseEnd_3744435 := by
    simpa [prefixWord, tailWord_3744435, baseEnd_3744435] using wordTrace_append hprefix tailTrace_3744435
  have hstable : (prefixWord ++ tailWord_3744435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744435).length < 2 ^ (prefixWord ++ tailWord_3744435).sum := by decide
  have hdescent : baseEnd_3744435 < baseStart_3744435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744452 : List Nat := [2, 3, 3, 1, 1, 2, 1, 9]
def baseStart_3744452 : Nat := 118140960795 + 3744452 * 2 ^ 59
def prefixEnd_3744452 : Nat := 4983230072969 + 3 ^ 40 * 3744452 * 2
def baseEnd_3744452 : Nat := 142422493606614003557747

theorem tailTrace_3744452 : CollatzResearch.WordTrace tailWord_3744452 prefixEnd_3744452 142422493606614003557747 := by
  unfold tailWord_3744452
  simp only [CollatzResearch.WordTrace]
  refine ⟨68285692115248690166697805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91047589486998253555597073 68285692115248690166697805)
  ·
    refine ⟨25607134543218258812511677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68285692115248690166697805 25607134543218258812511677)
    ·
      refine ⟨9602675453706847054691879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25607134543218258812511677 9602675453706847054691879)
      ·
        refine ⟨14404013180560270582037819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9602675453706847054691879 14404013180560270582037819)
        ·
          refine ⟨21606019770840405873056729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14404013180560270582037819 21606019770840405873056729)
          ·
            refine ⟨16204514828130304404792547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21606019770840405873056729 16204514828130304404792547)
            ·
              refine ⟨24306772242195456607188821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16204514828130304404792547 24306772242195456607188821)
              ·
                refine ⟨142422493606614003557747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24306772242195456607188821 142422493606614003557747)
                ·
                  rfl

theorem cell22_3744452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 9].length) (baseStart_3744452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3744452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3744452 prefixEnd_3744452 := by exact prefixLift 3744452
  have htrace : WordTrace (prefixWord ++ tailWord_3744452) baseStart_3744452 baseEnd_3744452 := by
    simpa [prefixWord, tailWord_3744452, baseEnd_3744452] using wordTrace_append hprefix tailTrace_3744452
  have hstable : (prefixWord ++ tailWord_3744452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744452).length < 2 ^ (prefixWord ++ tailWord_3744452).sum := by decide
  have hdescent : baseEnd_3744452 < baseStart_3744452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744456 : List Nat := [2, 1, 3, 1, 2, 3, 4, 1, 2, 3]
def baseStart_3744456 : Nat := 118140960795 + 3744456 * 2 ^ 59
def prefixEnd_3744456 : Nat := 4983230072969 + 3 ^ 40 * 3744456 * 2
def baseEnd_3744456 : Nat := 1281803811741271354919711

theorem tailTrace_3744456 : CollatzResearch.WordTrace tailWord_3744456 prefixEnd_3744456 1281803811741271354919711 := by
  unfold tailWord_3744456
  simp only [CollatzResearch.WordTrace]
  refine ⟨68285765061241444508270611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91047686748321926011027481 68285765061241444508270611)
  ·
    refine ⟨102428647591862166762405917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68285765061241444508270611 102428647591862166762405917)
    ·
      refine ⟨38410742846948312535902219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102428647591862166762405917 38410742846948312535902219)
      ·
        refine ⟨57616114270422468803853329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38410742846948312535902219 57616114270422468803853329)
        ·
          refine ⟨43212085702816851602889997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57616114270422468803853329 43212085702816851602889997)
          ·
            refine ⟨16204532138556319351083749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43212085702816851602889997 16204532138556319351083749)
            ·
              refine ⟨3038349775979309878328203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16204532138556319351083749 3038349775979309878328203)
              ·
                refine ⟨4557524663968964817492305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3038349775979309878328203 4557524663968964817492305)
                ·
                  refine ⟨3418143497976723613119229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4557524663968964817492305 3418143497976723613119229)
                  ·
                    refine ⟨1281803811741271354919711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3418143497976723613119229 1281803811741271354919711)
                    ·
                      rfl

theorem cell22_3744456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 4, 1, 2, 3].length) (baseStart_3744456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3744456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3744456 prefixEnd_3744456 := by exact prefixLift 3744456
  have htrace : WordTrace (prefixWord ++ tailWord_3744456) baseStart_3744456 baseEnd_3744456 := by
    simpa [prefixWord, tailWord_3744456, baseEnd_3744456] using wordTrace_append hprefix tailTrace_3744456
  have hstable : (prefixWord ++ tailWord_3744456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744456).length < 2 ^ (prefixWord ++ tailWord_3744456).sum := by decide
  have hdescent : baseEnd_3744456 < baseStart_3744456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744527 : List Nat := [1, 1, 2, 1, 1, 1, 5, 3, 3, 4]
def baseStart_3744527 : Nat := 118140960795 + 3744527 * 2 ^ 59
def prefixEnd_3744527 : Nat := 4983230072969 + 3 ^ 40 * 3744527 * 2
def baseEnd_3744527 : Nat := 1281828116492250836394493

theorem tailTrace_3744527 : CollatzResearch.WordTrace tailWord_3744527 prefixEnd_3744527 1281828116492250836394493 := by
  unfold tailWord_3744527
  simp only [CollatzResearch.WordTrace]
  refine ⟨136574119705225668142375835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91049413136817112094917223 136574119705225668142375835)
  ·
    refine ⟨204861179557838502213563753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136574119705225668142375835 204861179557838502213563753)
    ·
      refine ⟨153645884668378876660172815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204861179557838502213563753 153645884668378876660172815)
      ·
        refine ⟨230468827002568314990259223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153645884668378876660172815 230468827002568314990259223)
        ·
          refine ⟨345703240503852472485388835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230468827002568314990259223 345703240503852472485388835)
          ·
            refine ⟨518554860755778708728083253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345703240503852472485388835 518554860755778708728083253)
            ·
              refine ⟨48614518195854253943257805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 518554860755778708728083253 48614518195854253943257805)
              ·
                refine ⟨18230444323445345228721677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48614518195854253943257805 18230444323445345228721677)
                ·
                  refine ⟨6836416621292004460770629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18230444323445345228721677 6836416621292004460770629)
                  ·
                    refine ⟨1281828116492250836394493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6836416621292004460770629 1281828116492250836394493)
                    ·
                      rfl

theorem cell22_3744527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 3, 4].length) (baseStart_3744527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3744527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3744527 prefixEnd_3744527 := by exact prefixLift 3744527
  have htrace : WordTrace (prefixWord ++ tailWord_3744527) baseStart_3744527 baseEnd_3744527 := by
    simpa [prefixWord, tailWord_3744527, baseEnd_3744527] using wordTrace_append hprefix tailTrace_3744527
  have hstable : (prefixWord ++ tailWord_3744527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744527).length < 2 ^ (prefixWord ++ tailWord_3744527).sum := by decide
  have hdescent : baseEnd_3744527 < baseStart_3744527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744548 : List Nat := [2, 3, 1, 3, 4, 1, 1, 2, 5]
def baseStart_3744548 : Nat := 118140960795 + 3744548 * 2 ^ 59
def prefixEnd_3744548 : Nat := 4983230072969 + 3 ^ 40 * 3744548 * 2
def baseEnd_3744548 : Nat := 427278435073804593873143

theorem tailTrace_3744548 : CollatzResearch.WordTrace tailWord_3744548 prefixEnd_3744548 427278435073804593873143 := by
  unfold tailWord_3744548
  simp only [CollatzResearch.WordTrace]
  refine ⟨68287442819074794364445149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91049923758766392485926865 68287442819074794364445149)
  ·
    refine ⟨25607791057153047886666931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68287442819074794364445149 25607791057153047886666931)
    ·
      refine ⟨38411686585729571830000397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25607791057153047886666931 38411686585729571830000397)
      ·
        refine ⟨14404382469648589436250149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38411686585729571830000397 14404382469648589436250149)
        ·
          refine ⟨2700821713059110519296903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14404382469648589436250149 2700821713059110519296903)
          ·
            refine ⟨4051232569588665778945355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2700821713059110519296903 4051232569588665778945355)
            ·
              refine ⟨6076848854382998668418033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4051232569588665778945355 6076848854382998668418033)
              ·
                refine ⟨4557636640787249001313525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6076848854382998668418033 4557636640787249001313525)
                ·
                  refine ⟨427278435073804593873143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4557636640787249001313525 427278435073804593873143)
                  ·
                    rfl

theorem cell22_3744548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 2, 5].length) (baseStart_3744548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3744548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3744548 prefixEnd_3744548 := by exact prefixLift 3744548
  have htrace : WordTrace (prefixWord ++ tailWord_3744548) baseStart_3744548 baseEnd_3744548 := by
    simpa [prefixWord, tailWord_3744548, baseEnd_3744548] using wordTrace_append hprefix tailTrace_3744548
  have hstable : (prefixWord ++ tailWord_3744548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744548).length < 2 ^ (prefixWord ++ tailWord_3744548).sum := by decide
  have hdescent : baseEnd_3744548 < baseStart_3744548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744593 : List Nat := [1, 2, 2, 1, 6, 2, 1, 3, 4]
def baseStart_3744593 : Nat := 118140960795 + 3744593 * 2 ^ 59
def prefixEnd_3744593 : Nat := 4983230072969 + 3 ^ 40 * 3744593 * 2
def baseEnd_3744593 : Nat := 427283569880349554748097

theorem tailTrace_3744593 : CollatzResearch.WordTrace tailWord_3744593 prefixEnd_3744593 427283569880349554748097 := by
  unfold tailWord_3744593
  simp only [CollatzResearch.WordTrace]
  refine ⟨136576526922986561414278433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91051017948657707609518955 136576526922986561414278433)
  ·
    refine ⟨102432395192239921060708825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136576526922986561414278433 102432395192239921060708825)
    ·
      refine ⟨76824296394179940795531619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102432395192239921060708825 76824296394179940795531619)
      ·
        refine ⟨115236444591269911193297429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76824296394179940795531619 115236444591269911193297429)
        ·
          refine ⟨5401708340215777087185817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 115236444591269911193297429 5401708340215777087185817)
          ·
            refine ⟨4051281255161832815389363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5401708340215777087185817 4051281255161832815389363)
            ·
              refine ⟨6076921882742749223084045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4051281255161832815389363 6076921882742749223084045)
              ·
                refine ⟨2278845706028530958656517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6076921882742749223084045 2278845706028530958656517)
                ·
                  refine ⟨427283569880349554748097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2278845706028530958656517 427283569880349554748097)
                  ·
                    rfl

theorem cell22_3744593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 3, 4].length) (baseStart_3744593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3744593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3744593 prefixEnd_3744593 := by exact prefixLift 3744593
  have htrace : WordTrace (prefixWord ++ tailWord_3744593) baseStart_3744593 baseEnd_3744593 := by
    simpa [prefixWord, tailWord_3744593, baseEnd_3744593] using wordTrace_append hprefix tailTrace_3744593
  have hstable : (prefixWord ++ tailWord_3744593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744593).length < 2 ^ (prefixWord ++ tailWord_3744593).sum := by decide
  have hdescent : baseEnd_3744593 < baseStart_3744593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744604 : List Nat := [2, 2, 4, 2, 1, 1, 10]
def baseStart_3744604 : Nat := 118140960795 + 3744604 * 2 ^ 59
def prefixEnd_3744604 : Nat := 4983230072969 + 3 ^ 40 * 3744604 * 2
def baseEnd_3744604 : Nat := 47476091672809196378491

theorem tailTrace_3744604 : CollatzResearch.WordTrace tailWord_3744604 prefixEnd_3744604 47476091672809196378491 := by
  unfold tailWord_3744604
  simp only [CollatzResearch.WordTrace]
  refine ⟨68288464062973355146464433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91051285417297806861952577 68288464062973355146464433)
  ·
    refine ⟨51216348047230016359848325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68288464062973355146464433 51216348047230016359848325)
    ·
      refine ⟨9603065258855628067471561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51216348047230016359848325 9603065258855628067471561)
      ·
        refine ⟨7202298944141721050603671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9603065258855628067471561 7202298944141721050603671)
        ·
          refine ⟨10803448416212581575905507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7202298944141721050603671 10803448416212581575905507)
          ·
            refine ⟨16205172624318872363858261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10803448416212581575905507 16205172624318872363858261)
            ·
              refine ⟨47476091672809196378491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16205172624318872363858261 47476091672809196378491)
              ·
                rfl

theorem cell22_3744604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 10].length) (baseStart_3744604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3744604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3744604 prefixEnd_3744604 := by exact prefixLift 3744604
  have htrace : WordTrace (prefixWord ++ tailWord_3744604) baseStart_3744604 baseEnd_3744604 := by
    simpa [prefixWord, tailWord_3744604, baseEnd_3744604] using wordTrace_append hprefix tailTrace_3744604
  have hstable : (prefixWord ++ tailWord_3744604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744604).length < 2 ^ (prefixWord ++ tailWord_3744604).sum := by decide
  have hdescent : baseEnd_3744604 < baseStart_3744604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744610 : List Nat := [3, 3, 2, 1, 3, 1, 3, 2, 4]
def baseStart_3744610 : Nat := 118140960795 + 3744610 * 2 ^ 59
def prefixEnd_3744610 : Nat := 4983230072969 + 3 ^ 40 * 3744610 * 2
def baseEnd_3744610 : Nat := 427285509696155428856413

theorem tailTrace_3744610 : CollatzResearch.WordTrace tailWord_3744610 prefixEnd_3744610 427285509696155428856413 := by
  unfold tailWord_3744610
  simp only [CollatzResearch.WordTrace]
  refine ⟨34144286740981243329411821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91051431309283315545098189 34144286740981243329411821)
  ·
    refine ⟨12804107527867966248529433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34144286740981243329411821 12804107527867966248529433)
    ·
      refine ⟨9603080645900974686397075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12804107527867966248529433 9603080645900974686397075)
      ·
        refine ⟨14404620968851462029595613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9603080645900974686397075 14404620968851462029595613)
        ·
          refine ⟨5401732863319298261098355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14404620968851462029595613 5401732863319298261098355)
          ·
            refine ⟨8102599294978947391647533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5401732863319298261098355 8102599294978947391647533)
            ·
              refine ⟨3038474735617105271867825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8102599294978947391647533 3038474735617105271867825)
              ·
                refine ⟨2278856051712828953900869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3038474735617105271867825 2278856051712828953900869)
                ·
                  refine ⟨427285509696155428856413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2278856051712828953900869 427285509696155428856413)
                  ·
                    rfl

theorem cell22_3744610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 3, 2, 4].length) (baseStart_3744610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3744610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3744610 prefixEnd_3744610 := by exact prefixLift 3744610
  have htrace : WordTrace (prefixWord ++ tailWord_3744610) baseStart_3744610 baseEnd_3744610 := by
    simpa [prefixWord, tailWord_3744610, baseEnd_3744610] using wordTrace_append hprefix tailTrace_3744610
  have hstable : (prefixWord ++ tailWord_3744610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744610).length < 2 ^ (prefixWord ++ tailWord_3744610).sum := by decide
  have hdescent : baseEnd_3744610 < baseStart_3744610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744632 : List Nat := [2, 1, 2, 1, 1, 1, 1, 4, 9]
def baseStart_3744632 : Nat := 118140960795 + 3744632 * 2 ^ 59
def prefixEnd_3744632 : Nat := 4983230072969 + 3 ^ 40 * 3744632 * 2
def baseEnd_3744632 : Nat := 427288020046021854173057

theorem tailTrace_3744632 : CollatzResearch.WordTrace tailWord_3744632 prefixEnd_3744632 427288020046021854173057 := by
  unfold tailWord_3744632
  simp only [CollatzResearch.WordTrace]
  refine ⟨68288974684922635537474075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91051966246563514049965433 68288974684922635537474075)
  ·
    refine ⟨102433462027383953306211113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68288974684922635537474075 102433462027383953306211113)
    ·
      refine ⟨76825096520537964979658335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102433462027383953306211113 76825096520537964979658335)
      ·
        refine ⟨115237644780806947469487503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76825096520537964979658335 115237644780806947469487503)
        ·
          refine ⟨172856467171210421204231255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115237644780806947469487503 172856467171210421204231255)
          ·
            refine ⟨259284700756815631806346883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172856467171210421204231255 259284700756815631806346883)
            ·
              refine ⟨388927051135223447709520325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259284700756815631806346883 388927051135223447709520325)
              ·
                refine ⟨72923822087854396445535061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 388927051135223447709520325 72923822087854396445535061)
                ·
                  refine ⟨427288020046021854173057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 72923822087854396445535061 427288020046021854173057)
                  ·
                    rfl

theorem cell22_3744632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 9].length) (baseStart_3744632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3744632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3744632 prefixEnd_3744632 := by exact prefixLift 3744632
  have htrace : WordTrace (prefixWord ++ tailWord_3744632) baseStart_3744632 baseEnd_3744632 := by
    simpa [prefixWord, tailWord_3744632, baseEnd_3744632] using wordTrace_append hprefix tailTrace_3744632
  have hstable : (prefixWord ++ tailWord_3744632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744632).length < 2 ^ (prefixWord ++ tailWord_3744632).sum := by decide
  have hdescent : baseEnd_3744632 < baseStart_3744632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744711 : List Nat := [1, 1, 4, 1, 1, 2, 3, 5, 4]
def baseStart_3744711 : Nat := 118140960795 + 3744711 * 2 ^ 59
def prefixEnd_3744711 : Nat := 4983230072969 + 3 ^ 40 * 3744711 * 2
def baseEnd_3744711 : Nat := 427297034484178563264643

theorem tailTrace_3744711 : CollatzResearch.WordTrace tailWord_3744711 prefixEnd_3744711 427297034484178563264643 := by
  unfold tailWord_3744711
  simp only [CollatzResearch.WordTrace]
  refine ⟨136580830736559067567073987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91053887157706045044715991 136580830736559067567073987)
  ·
    refine ⟨204871246104838601350610981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136580830736559067567073987 204871246104838601350610981)
    ·
      refine ⟨38413358644657237753239559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204871246104838601350610981 38413358644657237753239559)
      ·
        refine ⟨57620037966985856629859339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38413358644657237753239559 57620037966985856629859339)
        ·
          refine ⟨86430056950478784944789009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57620037966985856629859339 86430056950478784944789009)
          ·
            refine ⟨64822542712859088708591757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86430056950478784944789009 64822542712859088708591757)
            ·
              refine ⟨24308453517322158265721909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64822542712859088708591757 24308453517322158265721909)
              ·
                refine ⟨2278917517248952337411429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24308453517322158265721909 2278917517248952337411429)
                ·
                  refine ⟨427297034484178563264643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2278917517248952337411429 427297034484178563264643)
                  ·
                    rfl

theorem cell22_3744711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 5, 4].length) (baseStart_3744711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3744711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3744711 prefixEnd_3744711 := by exact prefixLift 3744711
  have htrace : WordTrace (prefixWord ++ tailWord_3744711) baseStart_3744711 baseEnd_3744711 := by
    simpa [prefixWord, tailWord_3744711, baseEnd_3744711] using wordTrace_append hprefix tailTrace_3744711
  have hstable : (prefixWord ++ tailWord_3744711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744711).length < 2 ^ (prefixWord ++ tailWord_3744711).sum := by decide
  have hdescent : baseEnd_3744711 < baseStart_3744711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744739 : List Nat := [1, 1, 1, 6, 1, 1, 2, 9]
def baseStart_3744739 : Nat := 118140960795 + 3744739 * 2 ^ 59
def prefixEnd_3744739 : Nat := 4983230072969 + 3 ^ 40 * 3744739 * 2
def baseEnd_3744739 : Nat := 142433409824972550010427

theorem tailTrace_3744739 : CollatzResearch.WordTrace tailWord_3744739 prefixEnd_3744739 142433409824972550010427 := by
  unfold tailWord_3744739
  simp only [CollatzResearch.WordTrace]
  refine ⟨136581851980457628349093271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91054567986971752232728847 136581851980457628349093271)
  ·
    refine ⟨204872777970686442523639907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136581851980457628349093271 204872777970686442523639907)
    ·
      refine ⟨307309166956029663785459861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204872777970686442523639907 307309166956029663785459861)
      ·
        refine ⟨14405117201063890489943431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 307309166956029663785459861 14405117201063890489943431)
        ·
          refine ⟨21607675801595835734915147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14405117201063890489943431 21607675801595835734915147)
          ·
            refine ⟨32411513702393753602372721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21607675801595835734915147 32411513702393753602372721)
            ·
              refine ⟨24308635276795315201779541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32411513702393753602372721 24308635276795315201779541)
              ·
                refine ⟨142433409824972550010427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24308635276795315201779541 142433409824972550010427)
                ·
                  rfl

theorem cell22_3744739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 9].length) (baseStart_3744739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3744739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3744739 prefixEnd_3744739 := by exact prefixLift 3744739
  have htrace : WordTrace (prefixWord ++ tailWord_3744739) baseStart_3744739 baseEnd_3744739 := by
    simpa [prefixWord, tailWord_3744739, baseEnd_3744739] using wordTrace_append hprefix tailTrace_3744739
  have hstable : (prefixWord ++ tailWord_3744739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744739).length < 2 ^ (prefixWord ++ tailWord_3744739).sum := by decide
  have hdescent : baseEnd_3744739 < baseStart_3744739 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744743 : List Nat := [1, 1, 5, 2, 2, 3, 1, 1, 1, 5]
def baseStart_3744743 : Nat := 118140960795 + 3744743 * 2 ^ 59
def prefixEnd_3744743 : Nat := 4983230072969 + 3 ^ 40 * 3744743 * 2
def baseEnd_3744743 : Nat := 1281902057706498272993831

theorem tailTrace_3744743 : CollatzResearch.WordTrace tailWord_3744743 prefixEnd_3744743 1281902057706498272993831 := by
  unfold tailWord_3744743
  simp only [CollatzResearch.WordTrace]
  refine ⟨136581997872443137032238883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91054665248295424688159255 136581997872443137032238883)
  ·
    refine ⟨204872996808664705548358325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136581997872443137032238883 204872996808664705548358325)
    ·
      refine ⟨19206843450812316145158593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 204872996808664705548358325 19206843450812316145158593)
      ·
        refine ⟨14405132588109237108868945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19206843450812316145158593 14405132588109237108868945)
        ·
          refine ⟨10803849441081927831651709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14405132588109237108868945 10803849441081927831651709)
          ·
            refine ⟨4051443540405722936869391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10803849441081927831651709 4051443540405722936869391)
            ·
              refine ⟨6077165310608584405304087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4051443540405722936869391 6077165310608584405304087)
              ·
                refine ⟨9115747965912876607956131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6077165310608584405304087 9115747965912876607956131)
                ·
                  refine ⟨13673621948869314911934197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9115747965912876607956131 13673621948869314911934197)
                  ·
                    refine ⟨1281902057706498272993831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13673621948869314911934197 1281902057706498272993831)
                    ·
                      rfl

theorem cell22_3744743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 1, 1, 5].length) (baseStart_3744743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3744743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3744743 prefixEnd_3744743 := by exact prefixLift 3744743
  have htrace : WordTrace (prefixWord ++ tailWord_3744743) baseStart_3744743 baseEnd_3744743 := by
    simpa [prefixWord, tailWord_3744743, baseEnd_3744743] using wordTrace_append hprefix tailTrace_3744743
  have hstable : (prefixWord ++ tailWord_3744743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744743).length < 2 ^ (prefixWord ++ tailWord_3744743).sum := by decide
  have hdescent : baseEnd_3744743 < baseStart_3744743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744846 : List Nat := [4, 1, 1, 1, 1, 3, 2, 3, 6]
def baseStart_3744846 : Nat := 118140960795 + 3744846 * 2 ^ 59
def prefixEnd_3744846 : Nat := 4983230072969 + 3 ^ 40 * 3744846 * 2
def baseEnd_3744846 : Nat := 427312438903813445889505

theorem tailTrace_3744846 : CollatzResearch.WordTrace tailWord_3744846 prefixEnd_3744846 427312438903813445889505 := by
  unfold tailWord_3744846
  simp only [CollatzResearch.WordTrace]
  refine ⟨17073219323883748202904799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91057169727379990415492261 17073219323883748202904799)
  ·
    refine ⟨25609828985825622304357199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17073219323883748202904799 25609828985825622304357199)
    ·
      refine ⟨38414743478738433456535799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25609828985825622304357199 38414743478738433456535799)
      ·
        refine ⟨57622115218107650184803699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38414743478738433456535799 57622115218107650184803699)
        ·
          refine ⟨86433172827161475277205549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57622115218107650184803699 86433172827161475277205549)
          ·
            refine ⟨32412439810185553228952081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86433172827161475277205549 32412439810185553228952081)
            ·
              refine ⟨24309329857639164921714061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32412439810185553228952081 24309329857639164921714061)
              ·
                refine ⟨9115998696614686845642773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24309329857639164921714061 9115998696614686845642773)
                ·
                  refine ⟨427312438903813445889505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9115998696614686845642773 427312438903813445889505)
                  ·
                    rfl

theorem cell22_3744846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 3, 6].length) (baseStart_3744846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3744846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3744846 prefixEnd_3744846 := by exact prefixLift 3744846
  have htrace : WordTrace (prefixWord ++ tailWord_3744846) baseStart_3744846 baseEnd_3744846 := by
    simpa [prefixWord, tailWord_3744846, baseEnd_3744846] using wordTrace_append hprefix tailTrace_3744846
  have hstable : (prefixWord ++ tailWord_3744846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744846).length < 2 ^ (prefixWord ++ tailWord_3744846).sum := by decide
  have hdescent : baseEnd_3744846 < baseStart_3744846 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744876 : List Nat := [2, 2, 1, 1, 3, 2, 3, 1, 1, 6]
def baseStart_3744876 : Nat := 118140960795 + 3744876 * 2 ^ 59
def prefixEnd_3744876 : Nat := 4983230072969 + 3 ^ 40 * 3744876 * 2
def baseEnd_3744876 : Nat := 1281947586324530259418423

theorem tailTrace_3744876 : CollatzResearch.WordTrace tailWord_3744876 prefixEnd_3744876 1281947586324530259418423 := by
  unfold tailWord_3744876
  simp only [CollatzResearch.WordTrace]
  refine ⟨68293424390480650373415241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91057899187307533831220321 68293424390480650373415241)
  ·
    refine ⟨51220068292860487780061431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68293424390480650373415241 51220068292860487780061431)
    ·
      refine ⟨76830102439290731670092147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51220068292860487780061431 76830102439290731670092147)
      ·
        refine ⟨115245153658936097505138221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76830102439290731670092147 115245153658936097505138221)
        ·
          refine ⟨43216932622101036564426833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115245153658936097505138221 43216932622101036564426833)
          ·
            refine ⟨32412699466575777423320125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43216932622101036564426833 32412699466575777423320125)
            ·
              refine ⟨12154762299965916533745047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32412699466575777423320125 12154762299965916533745047)
              ·
                refine ⟨18232143449948874800617571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12154762299965916533745047 18232143449948874800617571)
                ·
                  refine ⟨27348215174923312200926357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18232143449948874800617571 27348215174923312200926357)
                  ·
                    refine ⟨1281947586324530259418423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27348215174923312200926357 1281947586324530259418423)
                    ·
                      rfl

theorem cell22_3744876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 6].length) (baseStart_3744876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3744876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3744876 prefixEnd_3744876 := by exact prefixLift 3744876
  have htrace : WordTrace (prefixWord ++ tailWord_3744876) baseStart_3744876 baseEnd_3744876 := by
    simpa [prefixWord, tailWord_3744876, baseEnd_3744876] using wordTrace_append hprefix tailTrace_3744876
  have hstable : (prefixWord ++ tailWord_3744876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744876).length < 2 ^ (prefixWord ++ tailWord_3744876).sum := by decide
  have hdescent : baseEnd_3744876 < baseStart_3744876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744878 : List Nat := [4, 1, 2, 2, 1, 2, 2, 2, 1, 5]
def baseStart_3744878 : Nat := 118140960795 + 3744878 * 2 ^ 59
def prefixEnd_3744878 : Nat := 4983230072969 + 3 ^ 40 * 3744878 * 2
def baseEnd_3744878 : Nat := 1281948270965402920868417

theorem tailTrace_3744878 : CollatzResearch.WordTrace tailWord_3744878 prefixEnd_3744878 1281948270965402920868417 := by
  unfold tailWord_3744878
  simp only [CollatzResearch.WordTrace]
  refine ⟨17073365215869256886050411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91057947817969370058935525 17073365215869256886050411)
  ·
    refine ⟨25610047823803885329075617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17073365215869256886050411 25610047823803885329075617)
    ·
      refine ⟨19207535867852913996806713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25610047823803885329075617 19207535867852913996806713)
      ·
        refine ⟨14405651900889685497605035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19207535867852913996806713 14405651900889685497605035)
        ·
          refine ⟨21608477851334528246407553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14405651900889685497605035 21608477851334528246407553)
          ·
            refine ⟨16206358388500896184805665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21608477851334528246407553 16206358388500896184805665)
            ·
              refine ⟨12154768791375672138604249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16206358388500896184805665 12154768791375672138604249)
              ·
                refine ⟨9116076593531754103953187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12154768791375672138604249 9116076593531754103953187)
                ·
                  refine ⟨13674114890297631155929781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9116076593531754103953187 13674114890297631155929781)
                  ·
                    refine ⟨1281948270965402920868417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13674114890297631155929781 1281948270965402920868417)
                    ·
                      rfl

theorem cell22_3744878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_3744878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3744878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3744878 prefixEnd_3744878 := by exact prefixLift 3744878
  have htrace : WordTrace (prefixWord ++ tailWord_3744878) baseStart_3744878 baseEnd_3744878 := by
    simpa [prefixWord, tailWord_3744878, baseEnd_3744878] using wordTrace_append hprefix tailTrace_3744878
  have hstable : (prefixWord ++ tailWord_3744878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744878).length < 2 ^ (prefixWord ++ tailWord_3744878).sum := by decide
  have hdescent : baseEnd_3744878 < baseStart_3744878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744940 : List Nat := [2, 2, 1, 1, 1, 1, 1, 9, 1, 3]
def baseStart_3744940 : Nat := 118140960795 + 3744940 * 2 ^ 59
def prefixEnd_3744940 : Nat := 4983230072969 + 3 ^ 40 * 3744940 * 2
def baseEnd_3744940 : Nat := 1281969494832455425818227

theorem tailTrace_3744940 : CollatzResearch.WordTrace tailWord_3744940 prefixEnd_3744940 1281969494832455425818227 := by
  unfold tailWord_3744940
  simp only [CollatzResearch.WordTrace]
  refine ⟨68294591526364719838580137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91059455368486293118106849 68294591526364719838580137)
  ·
    refine ⟨51220943644773539878935103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68294591526364719838580137 51220943644773539878935103)
    ·
      refine ⟨76831415467160309818402655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51220943644773539878935103 76831415467160309818402655)
      ·
        refine ⟨115247123200740464727603983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76831415467160309818402655 115247123200740464727603983)
        ·
          refine ⟨172870684801110697091405975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115247123200740464727603983 172870684801110697091405975)
          ·
            refine ⟨259306027201666045637108963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172870684801110697091405975 259306027201666045637108963)
            ·
              refine ⟨388959040802499068455663445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259306027201666045637108963 388959040802499068455663445)
              ·
                refine ⟨2279056879702142979232403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 388959040802499068455663445 2279056879702142979232403)
                ·
                  refine ⟨3418585319553214468848605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2279056879702142979232403 3418585319553214468848605)
                  ·
                    refine ⟨1281969494832455425818227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3418585319553214468848605 1281969494832455425818227)
                    ·
                      rfl

theorem cell22_3744940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 9, 1, 3].length) (baseStart_3744940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3744940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3744940 prefixEnd_3744940 := by exact prefixLift 3744940
  have htrace : WordTrace (prefixWord ++ tailWord_3744940) baseStart_3744940 baseEnd_3744940 := by
    simpa [prefixWord, tailWord_3744940, baseEnd_3744940] using wordTrace_append hprefix tailTrace_3744940
  have hstable : (prefixWord ++ tailWord_3744940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744940).length < 2 ^ (prefixWord ++ tailWord_3744940).sum := by decide
  have hdescent : baseEnd_3744940 < baseStart_3744940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744970 : List Nat := [3, 1, 2, 1, 3, 2, 4, 1, 5]
def baseStart_3744970 : Nat := 118140960795 + 3744970 * 2 ^ 59
def prefixEnd_3744970 : Nat := 4983230072969 + 3 ^ 40 * 3744970 * 2
def baseEnd_3744970 : Nat := 427326588148515115856045

theorem tailTrace_3744970 : CollatzResearch.WordTrace tailWord_3744970 prefixEnd_3744970 427326588148515115856045 := by
  unfold tailWord_3744970
  simp only [CollatzResearch.WordTrace]
  refine ⟨34147569310655188700188091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91060184828413836533834909 34147569310655188700188091)
  ·
    refine ⟨51221353965982783050282137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34147569310655188700188091 51221353965982783050282137)
    ·
      refine ⟨38416015474487087287711603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51221353965982783050282137 38416015474487087287711603)
      ·
        refine ⟨57624023211730630931567405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38416015474487087287711603 57624023211730630931567405)
        ·
          refine ⟨21609008704398986599337777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57624023211730630931567405 21609008704398986599337777)
          ·
            refine ⟨16206756528299239949503333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21609008704398986599337777 16206756528299239949503333)
            ·
              refine ⟨3038766849056107490531875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16206756528299239949503333 3038766849056107490531875)
              ·
                refine ⟨4558150273584161235797813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3038766849056107490531875 4558150273584161235797813)
                ·
                  refine ⟨427326588148515115856045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4558150273584161235797813 427326588148515115856045)
                  ·
                    rfl

theorem cell22_3744970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 4, 1, 5].length) (baseStart_3744970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3744970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3744970 prefixEnd_3744970 := by exact prefixLift 3744970
  have htrace : WordTrace (prefixWord ++ tailWord_3744970) baseStart_3744970 baseEnd_3744970 := by
    simpa [prefixWord, tailWord_3744970, baseEnd_3744970] using wordTrace_append hprefix tailTrace_3744970
  have hstable : (prefixWord ++ tailWord_3744970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744970).length < 2 ^ (prefixWord ++ tailWord_3744970).sum := by decide
  have hdescent : baseEnd_3744970 < baseStart_3744970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745064 : List Nat := [2, 1, 5, 1, 2, 3, 1, 2, 2, 3]
def baseStart_3745064 : Nat := 118140960795 + 3745064 * 2 ^ 59
def prefixEnd_3745064 : Nat := 4983230072969 + 3 ^ 40 * 3745064 * 2
def baseEnd_3745064 : Nat := 1282011942566560435717847

theorem tailTrace_3745064 : CollatzResearch.WordTrace tailWord_3745064 prefixEnd_3745064 1282011942566560435717847 := by
  unfold tailWord_3745064
  simp only [CollatzResearch.WordTrace]
  refine ⟨68296852852140104427337123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91062470469520139236449497 68296852852140104427337123)
  ·
    refine ⟨102445279278210156641005685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68296852852140104427337123 102445279278210156641005685)
    ·
      refine ⟨9604244932332202185094283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102445279278210156641005685 9604244932332202185094283)
      ·
        refine ⟨14406367398498303277641425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9604244932332202185094283 14406367398498303277641425)
        ·
          refine ⟨10804775548873727458231069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14406367398498303277641425 10804775548873727458231069)
          ·
            refine ⟨4051790830827647796836651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10804775548873727458231069 4051790830827647796836651)
            ·
              refine ⟨6077686246241471695254977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4051790830827647796836651 6077686246241471695254977)
              ·
                refine ⟨4558264684681103771441233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6077686246241471695254977 4558264684681103771441233)
                ·
                  refine ⟨3418698513510827828580925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4558264684681103771441233 3418698513510827828580925)
                  ·
                    refine ⟨1282011942566560435717847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3418698513510827828580925 1282011942566560435717847)
                    ·
                      rfl

theorem cell22_3745064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_3745064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3745064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3745064 prefixEnd_3745064 := by exact prefixLift 3745064
  have htrace : WordTrace (prefixWord ++ tailWord_3745064) baseStart_3745064 baseEnd_3745064 := by
    simpa [prefixWord, tailWord_3745064, baseEnd_3745064] using wordTrace_append hprefix tailTrace_3745064
  have hstable : (prefixWord ++ tailWord_3745064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745064).length < 2 ^ (prefixWord ++ tailWord_3745064).sum := by decide
  have hdescent : baseEnd_3745064 < baseStart_3745064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745075 : List Nat := [1, 1, 1, 2, 5, 2, 1, 3, 3, 3]
def baseStart_3745075 : Nat := 118140960795 + 3745075 * 2 ^ 59
def prefixEnd_3745075 : Nat := 4983230072969 + 3 ^ 40 * 3745075 * 2
def baseEnd_3745075 : Nat := 1282015708091360073692813

theorem tailTrace_3745075 : CollatzResearch.WordTrace tailWord_3745075 prefixEnd_3745075 1282015708091360073692813 := by
  unfold tailWord_3745075
  simp only [CollatzResearch.WordTrace]
  refine ⟨136594106907240357733324679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91062737938160238488883119 136594106907240357733324679)
  ·
    refine ⟨204891160360860536599987019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136594106907240357733324679 204891160360860536599987019)
    ·
      refine ⟨307336740541290804899980529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204891160360860536599987019 307336740541290804899980529)
      ·
        refine ⟨230502555405968103674985397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307336740541290804899980529 230502555405968103674985397)
        ·
          refine ⟨21609614569309509719529881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 230502555405968103674985397 21609614569309509719529881)
          ·
            refine ⟨16207210926982132289647411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21609614569309509719529881 16207210926982132289647411)
            ·
              refine ⟨24310816390473198434471117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16207210926982132289647411 24310816390473198434471117)
              ·
                refine ⟨9116556146427449412926669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24310816390473198434471117 9116556146427449412926669)
                ·
                  refine ⟨3418708554910293529847501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9116556146427449412926669 3418708554910293529847501)
                  ·
                    refine ⟨1282015708091360073692813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3418708554910293529847501 1282015708091360073692813)
                    ·
                      rfl

theorem cell22_3745075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 3, 3, 3].length) (baseStart_3745075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3745075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3745075 prefixEnd_3745075 := by exact prefixLift 3745075
  have htrace : WordTrace (prefixWord ++ tailWord_3745075) baseStart_3745075 baseEnd_3745075 := by
    simpa [prefixWord, tailWord_3745075, baseEnd_3745075] using wordTrace_append hprefix tailTrace_3745075
  have hstable : (prefixWord ++ tailWord_3745075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745075).length < 2 ^ (prefixWord ++ tailWord_3745075).sum := by decide
  have hdescent : baseEnd_3745075 < baseStart_3745075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745094 : List Nat := [6, 1, 1, 3, 1, 1, 1, 8]
def baseStart_3745094 : Nat := 118140960795 + 3745094 * 2 ^ 59
def prefixEnd_3745094 : Nat := 4983230072969 + 3 ^ 40 * 3745094 * 2
def baseEnd_3745094 : Nat := 142446912464405595274195

theorem tailTrace_3745094 : CollatzResearch.WordTrace tailWord_3745094 prefixEnd_3745094 142446912464405595274195 := by
  unfold tailWord_3745094
  simp only [CollatzResearch.WordTrace]
  refine ⟨4268587496692860124320823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 91063199929447682652177557 4268587496692860124320823)
  ·
    refine ⟨6402881245039290186481235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4268587496692860124320823 6402881245039290186481235)
    ·
      refine ⟨9604321867558935279721853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6402881245039290186481235 9604321867558935279721853)
      ·
        refine ⟨3601620700334600729895695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9604321867558935279721853 3601620700334600729895695)
        ·
          refine ⟨5402431050501901094843543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3601620700334600729895695 5402431050501901094843543)
          ·
            refine ⟨8103646575752851642265315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5402431050501901094843543 8103646575752851642265315)
            ·
              refine ⟨12155469863629277463397973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8103646575752851642265315 12155469863629277463397973)
              ·
                refine ⟨142446912464405595274195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12155469863629277463397973 142446912464405595274195)
                ·
                  rfl

theorem cell22_3745094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_3745094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3745094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3745094 prefixEnd_3745094 := by exact prefixLift 3745094
  have htrace : WordTrace (prefixWord ++ tailWord_3745094) baseStart_3745094 baseEnd_3745094 := by
    simpa [prefixWord, tailWord_3745094, baseEnd_3745094] using wordTrace_append hprefix tailTrace_3745094
  have hstable : (prefixWord ++ tailWord_3745094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745094).length < 2 ^ (prefixWord ++ tailWord_3745094).sum := by decide
  have hdescent : baseEnd_3745094 < baseStart_3745094 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745109 : List Nat := [1, 3, 2, 2, 3, 1, 3, 3, 1, 3]
def baseStart_3745109 : Nat := 118140960795 + 3745109 * 2 ^ 59
def prefixEnd_3745109 : Nat := 4983230072969 + 3 ^ 40 * 3745109 * 2
def baseEnd_3745109 : Nat := 1282027346986195318342709

theorem tailTrace_3745109 : CollatzResearch.WordTrace tailWord_3745109 prefixEnd_3745109 1282027346986195318342709 := by
  unfold tailWord_3745109
  simp only [CollatzResearch.WordTrace]
  refine ⟨136595346989117181540062381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91063564659411454360041587 136595346989117181540062381)
  ·
    refine ⟨51223255120918943077523393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136595346989117181540062381 51223255120918943077523393)
    ·
      refine ⟨38417441340689207308142545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51223255120918943077523393 38417441340689207308142545)
      ·
        refine ⟨28813081005516905481106909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38417441340689207308142545 28813081005516905481106909)
        ·
          refine ⟨10804905377068839555415091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28813081005516905481106909 10804905377068839555415091)
          ·
            refine ⟨16207358065603259333122637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10804905377068839555415091 16207358065603259333122637)
            ·
              refine ⟨6077759274601222249920989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16207358065603259333122637 6077759274601222249920989)
              ·
                refine ⟨2279159727975458343720371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6077759274601222249920989 2279159727975458343720371)
                ·
                  refine ⟨3418739591963187515580557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2279159727975458343720371 3418739591963187515580557)
                  ·
                    refine ⟨1282027346986195318342709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3418739591963187515580557 1282027346986195318342709)
                    ·
                      rfl

theorem cell22_3745109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 3, 1, 3].length) (baseStart_3745109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3745109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3745109 prefixEnd_3745109 := by exact prefixLift 3745109
  have htrace : WordTrace (prefixWord ++ tailWord_3745109) baseStart_3745109 baseEnd_3745109 := by
    simpa [prefixWord, tailWord_3745109, baseEnd_3745109] using wordTrace_append hprefix tailTrace_3745109
  have hstable : (prefixWord ++ tailWord_3745109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745109).length < 2 ^ (prefixWord ++ tailWord_3745109).sum := by decide
  have hdescent : baseEnd_3745109 < baseStart_3745109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745193 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 4, 7]
def baseStart_3745193 : Nat := 118140960795 + 3745193 * 2 ^ 59
def prefixEnd_3745193 : Nat := 4983230072969 + 3 ^ 40 * 3745193 * 2
def baseEnd_3745193 : Nat := 1282056101902847099242451

theorem tailTrace_3745193 : CollatzResearch.WordTrace tailWord_3745193 prefixEnd_3745193 1282056101902847099242451 := by
  unfold tailWord_3745193
  simp only [CollatzResearch.WordTrace]
  refine ⟨136598410720812863886120233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91065607147208575924080155 136598410720812863886120233)
  ·
    refine ⟨102448808040609647914590175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136598410720812863886120233 102448808040609647914590175)
    ·
      refine ⟨153673212060914471871885263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102448808040609647914590175 153673212060914471871885263)
      ·
        refine ⟨230509818091371707807827895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153673212060914471871885263 230509818091371707807827895)
        ·
          refine ⟨345764727137057561711741843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230509818091371707807827895 345764727137057561711741843)
          ·
            refine ⟨518647090705586342567612765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345764727137057561711741843 518647090705586342567612765)
            ·
              refine ⟨194492659014594878462854787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 518647090705586342567612765 194492659014594878462854787)
              ·
                refine ⟨291738988521892317694282181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194492659014594878462854787 291738988521892317694282181)
                ·
                  refine ⟨54701060347854809567677909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 291738988521892317694282181 54701060347854809567677909)
                  ·
                    refine ⟨1282056101902847099242451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54701060347854809567677909 1282056101902847099242451)
                    ·
                      rfl

theorem cell22_3745193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 7].length) (baseStart_3745193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3745193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3745193 prefixEnd_3745193 := by exact prefixLift 3745193
  have htrace : WordTrace (prefixWord ++ tailWord_3745193) baseStart_3745193 baseEnd_3745193 := by
    simpa [prefixWord, tailWord_3745193, baseEnd_3745193] using wordTrace_append hprefix tailTrace_3745193
  have hstable : (prefixWord ++ tailWord_3745193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745193).length < 2 ^ (prefixWord ++ tailWord_3745193).sum := by decide
  have hdescent : baseEnd_3745193 < baseStart_3745193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745351 : List Nat := [1, 1, 4, 1, 5, 1, 2, 2, 2, 3]
def baseStart_3745351 : Nat := 118140960795 + 3745351 * 2 ^ 59
def prefixEnd_3745351 : Nat := 4983230072969 + 3 ^ 40 * 3745351 * 2
def baseEnd_3745351 : Nat := 1282110188531787353791967

theorem tailTrace_3745351 : CollatzResearch.WordTrace tailWord_3745351 prefixEnd_3745351 1282110188531787353791967 := by
  unfold tailWord_3745351
  simp only [CollatzResearch.WordTrace]
  refine ⟨136604173454240456870371907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91069448969493637913581271 136604173454240456870371907)
  ·
    refine ⟨204906260181360685305557861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136604173454240456870371907 204906260181360685305557861)
    ·
      refine ⟨38419923784005128494792099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204906260181360685305557861 38419923784005128494792099)
      ·
        refine ⟨57629885676007692742188149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38419923784005128494792099 57629885676007692742188149)
        ·
          refine ⟨5402801782125721194580139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57629885676007692742188149 5402801782125721194580139)
          ·
            refine ⟨8104202673188581791870209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5402801782125721194580139 8104202673188581791870209)
            ·
              refine ⟨6078152004891436343902657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8104202673188581791870209 6078152004891436343902657)
              ·
                refine ⟨4558614003668577257926993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6078152004891436343902657 4558614003668577257926993)
                ·
                  refine ⟨3418960502751432943445245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4558614003668577257926993 3418960502751432943445245)
                  ·
                    refine ⟨1282110188531787353791967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3418960502751432943445245 1282110188531787353791967)
                    ·
                      rfl

theorem cell22_3745351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 2, 2, 3].length) (baseStart_3745351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3745351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3745351 prefixEnd_3745351 := by exact prefixLift 3745351
  have htrace : WordTrace (prefixWord ++ tailWord_3745351) baseStart_3745351 baseEnd_3745351 := by
    simpa [prefixWord, tailWord_3745351, baseEnd_3745351] using wordTrace_append hprefix tailTrace_3745351
  have hstable : (prefixWord ++ tailWord_3745351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745351).length < 2 ^ (prefixWord ++ tailWord_3745351).sum := by decide
  have hdescent : baseEnd_3745351 < baseStart_3745351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745360 : List Nat := [2, 1, 1, 1, 1, 3, 3, 1, 1, 8]
def baseStart_3745360 : Nat := 118140960795 + 3745360 * 2 ^ 59
def prefixEnd_3745360 : Nat := 4983230072969 + 3 ^ 40 * 3745360 * 2
def baseEnd_3745360 : Nat := 1282113269415714330316939

theorem tailTrace_3745360 : CollatzResearch.WordTrace tailWord_3745360 prefixEnd_3745360 1282113269415714330316939 := by
  unfold tailWord_3745360
  simp only [CollatzResearch.WordTrace]
  refine ⟨68302250855603925703724767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91069667807471900938299689 68302250855603925703724767)
  ·
    refine ⟨102453376283405888555587151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68302250855603925703724767 102453376283405888555587151)
    ·
      refine ⟨153680064425108832833380727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102453376283405888555587151 153680064425108832833380727)
      ·
        refine ⟨230520096637663249250071091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153680064425108832833380727 230520096637663249250071091)
        ·
          refine ⟨345780144956494873875106637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230520096637663249250071091 345780144956494873875106637)
          ·
            refine ⟨129667554358685577703164989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 345780144956494873875106637 129667554358685577703164989)
            ·
              refine ⟨48625332884507091638686871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129667554358685577703164989 48625332884507091638686871)
              ·
                refine ⟨72937999326760637458030307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48625332884507091638686871 72937999326760637458030307)
                ·
                  refine ⟨109406998990140956187045461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72937999326760637458030307 109406998990140956187045461)
                  ·
                    refine ⟨1282113269415714330316939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 109406998990140956187045461 1282113269415714330316939)
                    ·
                      rfl

theorem cell22_3745360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 1, 8].length) (baseStart_3745360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3745360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3745360 prefixEnd_3745360 := by exact prefixLift 3745360
  have htrace : WordTrace (prefixWord ++ tailWord_3745360) baseStart_3745360 baseEnd_3745360 := by
    simpa [prefixWord, tailWord_3745360, baseEnd_3745360] using wordTrace_append hprefix tailTrace_3745360
  have hstable : (prefixWord ++ tailWord_3745360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745360).length < 2 ^ (prefixWord ++ tailWord_3745360).sum := by decide
  have hdescent : baseEnd_3745360 < baseStart_3745360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745375 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 11]
def baseStart_3745375 : Nat := 118140960795 + 3745375 * 2 ^ 59
def prefixEnd_3745375 : Nat := 4983230072969 + 3 ^ 40 * 3745375 * 2
def baseEnd_3745375 : Nat := 427372801407419763730631

theorem tailTrace_3745375 : CollatzResearch.WordTrace tailWord_3745375 prefixEnd_3745375 427372801407419763730631 := by
  unfold tailWord_3745375
  simp only [CollatzResearch.WordTrace]
  refine ⟨136605048806153508969245579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91070032537435672646163719 136605048806153508969245579)
  ·
    refine ⟨204907573209230263453868369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136605048806153508969245579 204907573209230263453868369)
    ·
      refine ⟨153680679906922697590401277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204907573209230263453868369 153680679906922697590401277)
      ·
        refine ⟨57630254965096011596400479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153680679906922697590401277 57630254965096011596400479)
        ·
          refine ⟨86445382447644017394600719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57630254965096011596400479 86445382447644017394600719)
          ·
            refine ⟨129668073671466026091901079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86445382447644017394600719 129668073671466026091901079)
            ·
              refine ⟨194502110507199039137851619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129668073671466026091901079 194502110507199039137851619)
              ·
                refine ⟨291753165760798558706777429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194502110507199039137851619 291753165760798558706777429)
                ·
                  refine ⟨427372801407419763730631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 291753165760798558706777429 427372801407419763730631)
                  ·
                    rfl

theorem cell22_3745375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 11].length) (baseStart_3745375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3745375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3745375 prefixEnd_3745375 := by exact prefixLift 3745375
  have htrace : WordTrace (prefixWord ++ tailWord_3745375) baseStart_3745375 baseEnd_3745375 := by
    simpa [prefixWord, tailWord_3745375, baseEnd_3745375] using wordTrace_append hprefix tailTrace_3745375
  have hstable : (prefixWord ++ tailWord_3745375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745375).length < 2 ^ (prefixWord ++ tailWord_3745375).sum := by decide
  have hdescent : baseEnd_3745375 < baseStart_3745375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745379 : List Nat := [1, 1, 1, 5, 1, 4, 1, 2, 3, 3]
def baseStart_3745379 : Nat := 118140960795 + 3745379 * 2 ^ 59
def prefixEnd_3745379 : Nat := 4983230072969 + 3 ^ 40 * 3745379 * 2
def baseEnd_3745379 : Nat := 1282119773504004614091881

theorem tailTrace_3745379 : CollatzResearch.WordTrace tailWord_3745379 prefixEnd_3745379 1282119773504004614091881 := by
  unfold tailWord_3745379
  simp only [CollatzResearch.WordTrace]
  refine ⟨136605194698139017652391191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91070129798759345101594127 136605194698139017652391191)
  ·
    refine ⟨204907792047208526478586787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136605194698139017652391191 204907792047208526478586787)
    ·
      refine ⟨307361688070812789717880181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204907792047208526478586787 307361688070812789717880181)
      ·
        refine ⟨28815158256638699036051267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 307361688070812789717880181 28815158256638699036051267)
        ·
          refine ⟨43222737384958048554076901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28815158256638699036051267 43222737384958048554076901)
          ·
            refine ⟨8104263259679634103889419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43222737384958048554076901 8104263259679634103889419)
            ·
              refine ⟨12156394889519451155834129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8104263259679634103889419 12156394889519451155834129)
              ·
                refine ⟨9117296167139588366875597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12156394889519451155834129 9117296167139588366875597)
                ·
                  refine ⟨3418986062677345637578349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9117296167139588366875597 3418986062677345637578349)
                  ·
                    refine ⟨1282119773504004614091881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3418986062677345637578349 1282119773504004614091881)
                    ·
                      rfl

theorem cell22_3745379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 2, 3, 3].length) (baseStart_3745379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3745379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3745379 prefixEnd_3745379 := by exact prefixLift 3745379
  have htrace : WordTrace (prefixWord ++ tailWord_3745379) baseStart_3745379 baseEnd_3745379 := by
    simpa [prefixWord, tailWord_3745379, baseEnd_3745379] using wordTrace_append hprefix tailTrace_3745379
  have hstable : (prefixWord ++ tailWord_3745379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745379).length < 2 ^ (prefixWord ++ tailWord_3745379).sum := by decide
  have hdescent : baseEnd_3745379 < baseStart_3745379 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745409 : List Nat := [1, 2, 4, 2, 1, 2, 3, 2, 5]
def baseStart_3745409 : Nat := 118140960795 + 3745409 * 2 ^ 59
def prefixEnd_3745409 : Nat := 4983230072969 + 3 ^ 40 * 3745409 * 2
def baseEnd_3745409 : Nat := 427376681039031511947263

theorem tailTrace_3745409 : CollatzResearch.WordTrace tailWord_3745409 prefixEnd_3745409 427376681039031511947263 := by
  unfold tailWord_3745409
  simp only [CollatzResearch.WordTrace]
  refine ⟨136606288888030332775983281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91070859258686888517322187 136606288888030332775983281)
  ·
    refine ⟨102454716666022749581987461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136606288888030332775983281 102454716666022749581987461)
    ·
      refine ⟨19210259374879265546622649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102454716666022749581987461 19210259374879265546622649)
      ·
        refine ⟨14407694531159449159966987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19210259374879265546622649 14407694531159449159966987)
        ·
          refine ⟨21611541796739173739950481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14407694531159449159966987 21611541796739173739950481)
          ·
            refine ⟨16208656347554380304962861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21611541796739173739950481 16208656347554380304962861)
            ·
              refine ⟨6078246130332892614361073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16208656347554380304962861 6078246130332892614361073)
              ·
                refine ⟨4558684597749669460770805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6078246130332892614361073 4558684597749669460770805)
                ·
                  refine ⟨427376681039031511947263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4558684597749669460770805 427376681039031511947263)
                  ·
                    rfl

theorem cell22_3745409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 2, 5].length) (baseStart_3745409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3745409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3745409 prefixEnd_3745409 := by exact prefixLift 3745409
  have htrace : WordTrace (prefixWord ++ tailWord_3745409) baseStart_3745409 baseEnd_3745409 := by
    simpa [prefixWord, tailWord_3745409, baseEnd_3745409] using wordTrace_append hprefix tailTrace_3745409
  have hstable : (prefixWord ++ tailWord_3745409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745409).length < 2 ^ (prefixWord ++ tailWord_3745409).sum := by decide
  have hdescent : baseEnd_3745409 < baseStart_3745409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745469 : List Nat := [1, 4, 1, 2, 1, 2, 1, 3, 4, 3]
def baseStart_3745469 : Nat := 118140960795 + 3745469 * 2 ^ 59
def prefixEnd_3745469 : Nat := 4983230072969 + 3 ^ 40 * 3745469 * 2
def baseEnd_3745469 : Nat := 1282150582343274379341605

theorem tailTrace_3745469 : CollatzResearch.WordTrace tailWord_3745469 prefixEnd_3745469 1282150582343274379341605 := by
  unfold tailWord_3745469
  simp only [CollatzResearch.WordTrace]
  refine ⟨136608477267812963023167461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91072318178541975348778307 136608477267812963023167461)
  ·
    refine ⟨25614089487714930566843899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136608477267812963023167461 25614089487714930566843899)
    ·
      refine ⟨38421134231572395850265849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25614089487714930566843899 38421134231572395850265849)
      ·
        refine ⟨28815850673679296887699387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38421134231572395850265849 28815850673679296887699387)
        ·
          refine ⟨43223776010518945331549081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28815850673679296887699387 43223776010518945331549081)
          ·
            refine ⟨32417832007889208998661811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43223776010518945331549081 32417832007889208998661811)
            ·
              refine ⟨48626748011833813497992717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32417832007889208998661811 48626748011833813497992717)
              ·
                refine ⟨18235030504437680061747269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48626748011833813497992717 18235030504437680061747269)
                ·
                  refine ⟨3419068219582065011577613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18235030504437680061747269 3419068219582065011577613)
                  ·
                    refine ⟨1282150582343274379341605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3419068219582065011577613 1282150582343274379341605)
                    ·
                      rfl

theorem cell22_3745469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 4, 3].length) (baseStart_3745469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3745469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3745469 prefixEnd_3745469 := by exact prefixLift 3745469
  have htrace : WordTrace (prefixWord ++ tailWord_3745469) baseStart_3745469 baseEnd_3745469 := by
    simpa [prefixWord, tailWord_3745469, baseEnd_3745469] using wordTrace_append hprefix tailTrace_3745469
  have hstable : (prefixWord ++ tailWord_3745469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745469).length < 2 ^ (prefixWord ++ tailWord_3745469).sum := by decide
  have hdescent : baseEnd_3745469 < baseStart_3745469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745471 : List Nat := [1, 1, 2, 2, 2, 3, 5, 2, 4]
def baseStart_3745471 : Nat := 118140960795 + 3745471 * 2 ^ 59
def prefixEnd_3745471 : Nat := 4983230072969 + 3 ^ 40 * 3745471 * 2
def baseEnd_3745471 : Nat := 427383755661382346930533

theorem tailTrace_3745471 : CollatzResearch.WordTrace tailWord_3745471 prefixEnd_3745471 427383755661382346930533 := by
  unfold tailWord_3745471
  simp only [CollatzResearch.WordTrace]
  refine ⟨136608550213805717364740267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91072366809203811576493511 136608550213805717364740267)
  ·
    refine ⟨204912825320708576047110401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136608550213805717364740267 204912825320708576047110401)
    ·
      refine ⟨153684618990531432035332801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204912825320708576047110401 153684618990531432035332801)
      ·
        refine ⟨115263464242898574026499601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153684618990531432035332801 115263464242898574026499601)
        ·
          refine ⟨86447598182173930519874701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115263464242898574026499601 86447598182173930519874701)
          ·
            refine ⟨32417849318315223944953013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86447598182173930519874701 32417849318315223944953013)
            ·
              refine ⟨3039173373592052244839345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32417849318315223944953013 3039173373592052244839345)
              ·
                refine ⟨2279380030194039183629509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3039173373592052244839345 2279380030194039183629509)
                ·
                  refine ⟨427383755661382346930533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2279380030194039183629509 427383755661382346930533)
                  ·
                    rfl

theorem cell22_3745471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 5, 2, 4].length) (baseStart_3745471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3745471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3745471 prefixEnd_3745471 := by exact prefixLift 3745471
  have htrace : WordTrace (prefixWord ++ tailWord_3745471) baseStart_3745471 baseEnd_3745471 := by
    simpa [prefixWord, tailWord_3745471, baseEnd_3745471] using wordTrace_append hprefix tailTrace_3745471
  have hstable : (prefixWord ++ tailWord_3745471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745471).length < 2 ^ (prefixWord ++ tailWord_3745471).sum := by decide
  have hdescent : baseEnd_3745471 < baseStart_3745471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745486 : List Nat := [4, 1, 1, 1, 3, 1, 3, 3, 2, 3]
def baseStart_3745486 : Nat := 118140960795 + 3745486 * 2 ^ 59
def prefixEnd_3745486 : Nat := 4983230072969 + 3 ^ 40 * 3745486 * 2
def baseEnd_3745486 : Nat := 1282156401790692001666553

theorem tailTrace_3745486 : CollatzResearch.WordTrace tailWord_3745486 prefixEnd_3745486 1282156401790692001666553 := by
  unfold tailWord_3745486
  simp only [CollatzResearch.WordTrace]
  refine ⟨17076137163593921865817039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91072731539167583284357541 17076137163593921865817039)
  ·
    refine ⟨25614205745390882798725559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17076137163593921865817039 25614205745390882798725559)
    ·
      refine ⟨38421308618086324198088339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25614205745390882798725559 38421308618086324198088339)
      ·
        refine ⟨57631962927129486297132509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38421308618086324198088339 57631962927129486297132509)
        ·
          refine ⟨21611986097673557361424691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57631962927129486297132509 21611986097673557361424691)
          ·
            refine ⟨32417979146510336042137037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21611986097673557361424691 32417979146510336042137037)
            ·
              refine ⟨12156742179941376015801389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32417979146510336042137037 12156742179941376015801389)
              ·
                refine ⟨4558778317478016005925521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12156742179941376015801389 4558778317478016005925521)
                ·
                  refine ⟨3419083738108512004444141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4558778317478016005925521 3419083738108512004444141)
                  ·
                    refine ⟨1282156401790692001666553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3419083738108512004444141 1282156401790692001666553)
                    ·
                      rfl

theorem cell22_3745486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 3, 2, 3].length) (baseStart_3745486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3745486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3745486 prefixEnd_3745486 := by exact prefixLift 3745486
  have htrace : WordTrace (prefixWord ++ tailWord_3745486) baseStart_3745486 baseEnd_3745486 := by
    simpa [prefixWord, tailWord_3745486, baseEnd_3745486] using wordTrace_append hprefix tailTrace_3745486
  have hstable : (prefixWord ++ tailWord_3745486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745486).length < 2 ^ (prefixWord ++ tailWord_3745486).sum := by decide
  have hdescent : baseEnd_3745486 < baseStart_3745486 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745527 : List Nat := [1, 1, 3, 1, 1, 1, 4, 3, 7]
def baseStart_3745527 : Nat := 118140960795 + 3745527 * 2 ^ 59
def prefixEnd_3745527 : Nat := 4983230072969 + 3 ^ 40 * 3745527 * 2
def baseEnd_3745527 : Nat := 427390145642860520463809

theorem tailTrace_3745527 : CollatzResearch.WordTrace tailWord_3745527 prefixEnd_3745527 427390145642860520463809 := by
  unfold tailWord_3745527
  simp only [CollatzResearch.WordTrace]
  refine ⟨136610592701602838928778835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91073728467735225952519223 136610592701602838928778835)
  ·
    refine ⟨204915889052404258393168253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136610592701602838928778835 204915889052404258393168253)
    ·
      refine ⟨76843458394651596897438095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204915889052404258393168253 76843458394651596897438095)
      ·
        refine ⟨115265187591977395346157143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76843458394651596897438095 115265187591977395346157143)
        ·
          refine ⟨172897781387966093019235715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115265187591977395346157143 172897781387966093019235715)
          ·
            refine ⟨259346672081949139528853573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172897781387966093019235715 259346672081949139528853573)
            ·
              refine ⟨48627501015365463661660045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 259346672081949139528853573 48627501015365463661660045)
              ·
                refine ⟨18235312880762048873122517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48627501015365463661660045 18235312880762048873122517)
                ·
                  refine ⟨427390145642860520463809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18235312880762048873122517 427390145642860520463809)
                  ·
                    rfl

theorem cell22_3745527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 7].length) (baseStart_3745527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3745527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3745527 prefixEnd_3745527 := by exact prefixLift 3745527
  have htrace : WordTrace (prefixWord ++ tailWord_3745527) baseStart_3745527 baseEnd_3745527 := by
    simpa [prefixWord, tailWord_3745527, baseEnd_3745527] using wordTrace_append hprefix tailTrace_3745527
  have hstable : (prefixWord ++ tailWord_3745527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745527).length < 2 ^ (prefixWord ++ tailWord_3745527).sum := by decide
  have hdescent : baseEnd_3745527 < baseStart_3745527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745544 : List Nat := [2, 1, 3, 2, 2, 1, 1, 5, 5]
def baseStart_3745544 : Nat := 118140960795 + 3745544 * 2 ^ 59
def prefixEnd_3745544 : Nat := 4983230072969 + 3 ^ 40 * 3745544 * 2
def baseEnd_3745544 : Nat := 427392085458666394572125

theorem tailTrace_3745544 : CollatzResearch.WordTrace tailWord_3745544 prefixEnd_3745544 427392085458666394572125 := by
  unfold tailWord_3745544
  simp only [CollatzResearch.WordTrace]
  refine ⟨68305606371270625416073843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91074141828360833888098457 68305606371270625416073843)
  ·
    refine ⟨102458409556905938124110765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68305606371270625416073843 102458409556905938124110765)
    ·
      refine ⟨38421903583839726796541537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102458409556905938124110765 38421903583839726796541537)
      ·
        refine ⟨28816427687879795097406153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38421903583839726796541537 28816427687879795097406153)
        ·
          refine ⟨21612320765909846323054615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28816427687879795097406153 21612320765909846323054615)
          ·
            refine ⟨32418481148864769484581923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21612320765909846323054615 32418481148864769484581923)
            ·
              refine ⟨48627721723297154226872885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32418481148864769484581923 48627721723297154226872885)
              ·
                refine ⟨4558848911559108208769333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48627721723297154226872885 4558848911559108208769333)
                ·
                  refine ⟨427392085458666394572125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4558848911559108208769333 427392085458666394572125)
                  ·
                    rfl

theorem cell22_3745544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 5, 5].length) (baseStart_3745544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3745544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3745544 prefixEnd_3745544 := by exact prefixLift 3745544
  have htrace : WordTrace (prefixWord ++ tailWord_3745544) baseStart_3745544 baseEnd_3745544 := by
    simpa [prefixWord, tailWord_3745544, baseEnd_3745544] using wordTrace_append hprefix tailTrace_3745544
  have hstable : (prefixWord ++ tailWord_3745544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745544).length < 2 ^ (prefixWord ++ tailWord_3745544).sum := by decide
  have hdescent : baseEnd_3745544 < baseStart_3745544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745621 : List Nat := [1, 3, 2, 2, 2, 2, 1, 2, 4, 3]
def baseStart_3745621 : Nat := 118140960795 + 3745621 * 2 ^ 59
def prefixEnd_3745621 : Nat := 4983230072969 + 3 ^ 40 * 3745621 * 2
def baseEnd_3745621 : Nat := 1282202615049596649541139

theorem tailTrace_3745621 : CollatzResearch.WordTrace tailWord_3745621 prefixEnd_3745621 1282202615049596649541139 := by
  unfold tailWord_3745621
  simp only [CollatzResearch.WordTrace]
  refine ⟨136614021163262292982700717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91076014108841528655133811 136614021163262292982700717)
  ·
    refine ⟨51230257936223359868512769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136614021163262292982700717 51230257936223359868512769)
    ·
      refine ⟨38422693452167519901384577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51230257936223359868512769 38422693452167519901384577)
      ·
        refine ⟨28817020089125639926038433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38422693452167519901384577 28817020089125639926038433)
        ·
          refine ⟨21612765066844229944528825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28817020089125639926038433 21612765066844229944528825)
          ·
            refine ⟨16209573800133172458396619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21612765066844229944528825 16209573800133172458396619)
            ·
              refine ⟨24314360700199758687594929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16209573800133172458396619 24314360700199758687594929)
              ·
                refine ⟨18235770525149819015696197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24314360700199758687594929 18235770525149819015696197)
                ·
                  refine ⟨3419206973465591065443037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18235770525149819015696197 3419206973465591065443037)
                  ·
                    refine ⟨1282202615049596649541139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3419206973465591065443037 1282202615049596649541139)
                    ·
                      rfl

theorem cell22_3745621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 4, 3].length) (baseStart_3745621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3745621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3745621 prefixEnd_3745621 := by exact prefixLift 3745621
  have htrace : WordTrace (prefixWord ++ tailWord_3745621) baseStart_3745621 baseEnd_3745621 := by
    simpa [prefixWord, tailWord_3745621, baseEnd_3745621] using wordTrace_append hprefix tailTrace_3745621
  have hstable : (prefixWord ++ tailWord_3745621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745621).length < 2 ^ (prefixWord ++ tailWord_3745621).sum := by decide
  have hdescent : baseEnd_3745621 < baseStart_3745621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745700 : List Nat := [2, 3, 1, 2, 1, 4, 1, 4, 1, 3]
def baseStart_3745700 : Nat := 118140960795 + 3745700 * 2 ^ 59
def prefixEnd_3745700 : Nat := 4983230072969 + 3 ^ 40 * 3745700 * 2
def baseEnd_3745700 : Nat := 1282229658364066776815897

theorem tailTrace_3745700 : CollatzResearch.WordTrace tailWord_3745700 prefixEnd_3745700 1282229658364066776815897 := by
  unfold tailWord_3745700
  simp only [CollatzResearch.WordTrace]
  refine ⟨68308451264988044737413277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91077935019984059649884369 68308451264988044737413277)
  ·
    refine ⟨25615669224370516776529979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68308451264988044737413277 25615669224370516776529979)
    ·
      refine ⟨38423503836555775164794969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25615669224370516776529979 38423503836555775164794969)
      ·
        refine ⟨28817627877416831373596227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38423503836555775164794969 28817627877416831373596227)
        ·
          refine ⟨43226441816125247060394341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28817627877416831373596227 43226441816125247060394341)
          ·
            refine ⟨8104957840523483823823939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43226441816125247060394341 8104957840523483823823939)
            ·
              refine ⟨12157436760785225735735909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8104957840523483823823939 12157436760785225735735909)
              ·
                refine ⟨2279519392647229825450483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12157436760785225735735909 2279519392647229825450483)
                ·
                  refine ⟨3419279088970844738175725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2279519392647229825450483 3419279088970844738175725)
                  ·
                    refine ⟨1282229658364066776815897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3419279088970844738175725 1282229658364066776815897)
                    ·
                      rfl

theorem cell22_3745700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 4, 1, 3].length) (baseStart_3745700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3745700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3745700 prefixEnd_3745700 := by exact prefixLift 3745700
  have htrace : WordTrace (prefixWord ++ tailWord_3745700) baseStart_3745700 baseEnd_3745700 := by
    simpa [prefixWord, tailWord_3745700, baseEnd_3745700] using wordTrace_append hprefix tailTrace_3745700
  have hstable : (prefixWord ++ tailWord_3745700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745700).length < 2 ^ (prefixWord ++ tailWord_3745700).sum := by decide
  have hdescent : baseEnd_3745700 < baseStart_3745700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745790 : List Nat := [4, 2, 2, 2, 1, 1, 1, 2, 4, 3]
def baseStart_3745790 : Nat := 118140960795 + 3745790 * 2 ^ 59
def prefixEnd_3745790 : Nat := 4983230072969 + 3 ^ 40 * 3745790 * 2
def baseEnd_3745790 : Nat := 1282260467203336542065621

theorem tailTrace_3745790 : CollatzResearch.WordTrace tailWord_3745790 prefixEnd_3745790 1282260467203336542065621 := by
  unfold tailWord_3745790
  simp only [CollatzResearch.WordTrace]
  refine ⟨17077523137456254355700353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91080123399766689897068549 17077523137456254355700353)
  ·
    refine ⟨12808142353092190766775265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17077523137456254355700353 12808142353092190766775265)
    ·
      refine ⟨9606106764819143075081449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12808142353092190766775265 9606106764819143075081449)
      ·
        refine ⟨7204580073614357306311087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9606106764819143075081449 7204580073614357306311087)
        ·
          refine ⟨10806870110421535959466631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7204580073614357306311087 10806870110421535959466631)
          ·
            refine ⟨16210305165632303939199947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10806870110421535959466631 16210305165632303939199947)
            ·
              refine ⟨24315457748448455908799921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16210305165632303939199947 24315457748448455908799921)
              ·
                refine ⟨18236593311336341931599941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24315457748448455908799921 18236593311336341931599941)
                ·
                  refine ⟨3419361245875564112174989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18236593311336341931599941 3419361245875564112174989)
                  ·
                    refine ⟨1282260467203336542065621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3419361245875564112174989 1282260467203336542065621)
                    ·
                      rfl

theorem cell22_3745790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_3745790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3745790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3745790 prefixEnd_3745790 := by exact prefixLift 3745790
  have htrace : WordTrace (prefixWord ++ tailWord_3745790) baseStart_3745790 baseEnd_3745790 := by
    simpa [prefixWord, tailWord_3745790, baseEnd_3745790] using wordTrace_append hprefix tailTrace_3745790
  have hstable : (prefixWord ++ tailWord_3745790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745790).length < 2 ^ (prefixWord ++ tailWord_3745790).sum := by decide
  have hdescent : baseEnd_3745790 < baseStart_3745790 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745816 : List Nat := [2, 1, 2, 3, 2, 1, 2, 1, 2, 6]
def baseStart_3745816 : Nat := 118140960795 + 3745816 * 2 ^ 59
def prefixEnd_3745816 : Nat := 4983230072969 + 3 ^ 40 * 3745816 * 2
def baseEnd_3745816 : Nat := 1282269367534681140915541

theorem tailTrace_3745816 : CollatzResearch.WordTrace tailWord_3745816 prefixEnd_3745816 1282269367534681140915541 := by
  unfold tailWord_3745816
  simp only [CollatzResearch.WordTrace]
  refine ⟨68310566698777920643024651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91080755598370560857366201 68310566698777920643024651)
  ·
    refine ⟨102465850048166880964536977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68310566698777920643024651 102465850048166880964536977)
    ·
      refine ⟨76849387536125160723402733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102465850048166880964536977 76849387536125160723402733)
      ·
        refine ⟨28818520326046935271276025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76849387536125160723402733 28818520326046935271276025)
        ·
          refine ⟨21613890244535201453457019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28818520326046935271276025 21613890244535201453457019)
          ·
            refine ⟨32420835366802802180185529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21613890244535201453457019 32420835366802802180185529)
            ·
              refine ⟨24315626525102101635139147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32420835366802802180185529 24315626525102101635139147)
              ·
                refine ⟨36473439787653152452708721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24315626525102101635139147 36473439787653152452708721)
                ·
                  refine ⟨27355079840739864339531541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36473439787653152452708721 27355079840739864339531541)
                  ·
                    refine ⟨1282269367534681140915541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27355079840739864339531541 1282269367534681140915541)
                    ·
                      rfl

theorem cell22_3745816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 6].length) (baseStart_3745816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3745816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3745816 prefixEnd_3745816 := by exact prefixLift 3745816
  have htrace : WordTrace (prefixWord ++ tailWord_3745816) baseStart_3745816 baseEnd_3745816 := by
    simpa [prefixWord, tailWord_3745816, baseEnd_3745816] using wordTrace_append hprefix tailTrace_3745816
  have hstable : (prefixWord ++ tailWord_3745816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745816).length < 2 ^ (prefixWord ++ tailWord_3745816).sum := by decide
  have hdescent : baseEnd_3745816 < baseStart_3745816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745893 : List Nat := [1, 3, 1, 3, 2, 3, 1, 2, 6]
def baseStart_3745893 : Nat := 118140960795 + 3745893 * 2 ^ 59
def prefixEnd_3745893 : Nat := 4983230072969 + 3 ^ 40 * 3745893 * 2
def baseEnd_3745893 : Nat := 427431908736092868913435

theorem tailTrace_3745893 : CollatzResearch.WordTrace tailWord_3745893 prefixEnd_3745893 427431908736092868913435 := by
  unfold tailWord_3745893
  simp only [CollatzResearch.WordTrace]
  refine ⟨136623941818276883436602333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91082627878851255624401555 136623941818276883436602333)
  ·
    refine ⟨51233978181853831288725875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136623941818276883436602333 51233978181853831288725875)
    ·
      refine ⟨76850967272780746933088813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51233978181853831288725875 76850967272780746933088813)
      ·
        refine ⟨28819112727292780099908305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76850967272780746933088813 28819112727292780099908305)
        ·
          refine ⟨21614334545469585074931229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28819112727292780099908305 21614334545469585074931229)
          ·
            refine ⟨8105375454551094403099211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21614334545469585074931229 8105375454551094403099211)
            ·
              refine ⟨12158063181826641604648817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8105375454551094403099211 12158063181826641604648817)
              ·
                refine ⟨9118547386369981203486613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12158063181826641604648817 9118547386369981203486613)
                ·
                  refine ⟨427431908736092868913435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9118547386369981203486613 427431908736092868913435)
                  ·
                    rfl

theorem cell22_3745893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 2, 6].length) (baseStart_3745893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3745893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3745893 prefixEnd_3745893 := by exact prefixLift 3745893
  have htrace : WordTrace (prefixWord ++ tailWord_3745893) baseStart_3745893 baseEnd_3745893 := by
    simpa [prefixWord, tailWord_3745893, baseEnd_3745893] using wordTrace_append hprefix tailTrace_3745893
  have hstable : (prefixWord ++ tailWord_3745893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745893).length < 2 ^ (prefixWord ++ tailWord_3745893).sum := by decide
  have hdescent : baseEnd_3745893 < baseStart_3745893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745925 : List Nat := [1, 3, 1, 1, 5, 2, 1, 1, 4, 3]
def baseStart_3745925 : Nat := 118140960795 + 3745925 * 2 ^ 59
def prefixEnd_3745925 : Nat := 4983230072969 + 3 ^ 40 * 3745925 * 2
def baseEnd_3745925 : Nat := 1282306680462241189940207

theorem tailTrace_3745925 : CollatzResearch.WordTrace tailWord_3745925 prefixEnd_3745925 1282306680462241189940207 := by
  unfold tailWord_3745925
  simp only [CollatzResearch.WordTrace]
  refine ⟨136625108954160952901767229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91083405969440635267844819 136625108954160952901767229)
  ·
    refine ⟨51234415857810357338162711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136625108954160952901767229 51234415857810357338162711)
    ·
      refine ⟨76851623786715536007244067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51234415857810357338162711 76851623786715536007244067)
      ·
        refine ⟨115277435680073304010866101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76851623786715536007244067 115277435680073304010866101)
        ·
          refine ⟨10807259595006872251018697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 115277435680073304010866101 10807259595006872251018697)
          ·
            refine ⟨8105444696255154188264023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10807259595006872251018697 8105444696255154188264023)
            ·
              refine ⟨12158167044382731282396035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8105444696255154188264023 12158167044382731282396035)
              ·
                refine ⟨18237250566574096923594053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12158167044382731282396035 18237250566574096923594053)
                ·
                  refine ⟨3419484481232643173173885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18237250566574096923594053 3419484481232643173173885)
                  ·
                    refine ⟨1282306680462241189940207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3419484481232643173173885 1282306680462241189940207)
                    ·
                      rfl

theorem cell22_3745925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 4, 3].length) (baseStart_3745925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3745925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3745925 prefixEnd_3745925 := by exact prefixLift 3745925
  have htrace : WordTrace (prefixWord ++ tailWord_3745925) baseStart_3745925 baseEnd_3745925 := by
    simpa [prefixWord, tailWord_3745925, baseEnd_3745925] using wordTrace_append hprefix tailTrace_3745925
  have hstable : (prefixWord ++ tailWord_3745925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745925).length < 2 ^ (prefixWord ++ tailWord_3745925).sum := by decide
  have hdescent : baseEnd_3745925 < baseStart_3745925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745938 : List Nat := [3, 2, 3, 1, 1, 1, 2, 9]
def baseStart_3745938 : Nat := 118140960795 + 3745938 * 2 ^ 59
def prefixEnd_3745938 : Nat := 4983230072969 + 3 ^ 40 * 3745938 * 2
def baseEnd_3745938 : Nat := 142479014514212609929463

theorem tailTrace_3745938 : CollatzResearch.WordTrace tailWord_3745938 prefixEnd_3745938 142479014514212609929463 := by
  unfold tailWord_3745938
  simp only [CollatzResearch.WordTrace]
  refine ⟨34156395775778464030497617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91083722068742570747993645 34156395775778464030497617)
  ·
    refine ⟨25617296831833848022873213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34156395775778464030497617 25617296831833848022873213)
    ·
      refine ⟨9606486311937693008577455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25617296831833848022873213 9606486311937693008577455)
      ·
        refine ⟨14409729467906539512866183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9606486311937693008577455 14409729467906539512866183)
        ·
          refine ⟨21614594201859809269299275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14409729467906539512866183 21614594201859809269299275)
          ·
            refine ⟨32421891302789713903948913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21614594201859809269299275 32421891302789713903948913)
            ·
              refine ⟨24316418477092285427961685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32421891302789713903948913 24316418477092285427961685)
              ·
                refine ⟨142479014514212609929463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24316418477092285427961685 142479014514212609929463)
                ·
                  rfl

theorem cell22_3745938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 9].length) (baseStart_3745938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3745938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3745938 prefixEnd_3745938 := by exact prefixLift 3745938
  have htrace : WordTrace (prefixWord ++ tailWord_3745938) baseStart_3745938 baseEnd_3745938 := by
    simpa [prefixWord, tailWord_3745938, baseEnd_3745938] using wordTrace_append hprefix tailTrace_3745938
  have hstable : (prefixWord ++ tailWord_3745938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745938).length < 2 ^ (prefixWord ++ tailWord_3745938).sum := by decide
  have hdescent : baseEnd_3745938 < baseStart_3745938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745983 : List Nat := [1, 1, 2, 2, 2, 2, 1, 6, 5]
def baseStart_3745983 : Nat := 118140960795 + 3745983 * 2 ^ 59
def prefixEnd_3745983 : Nat := 4983230072969 + 3 ^ 40 * 3745983 * 2
def baseEnd_3745983 : Nat := 427442178349182790663343

theorem tailTrace_3745983 : CollatzResearch.WordTrace tailWord_3745983 prefixEnd_3745983 427442178349182790663343 := by
  unfold tailWord_3745983
  simp only [CollatzResearch.WordTrace]
  refine ⟨136627224387950828807378603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91084816258633885871585735 136627224387950828807378603)
  ·
    refine ⟨204940836581926243211067905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136627224387950828807378603 204940836581926243211067905)
    ·
      refine ⟨153705627436444682408300929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204940836581926243211067905 153705627436444682408300929)
      ·
        refine ⟨115279220577333511806225697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153705627436444682408300929 115279220577333511806225697)
        ·
          refine ⟨86459415433000133854669273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115279220577333511806225697 86459415433000133854669273)
          ·
            refine ⟨64844561574750100391001955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86459415433000133854669273 64844561574750100391001955)
            ·
              refine ⟨97266842362125150586502933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64844561574750100391001955 97266842362125150586502933)
              ·
                refine ⟨4559383235724616433742325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 97266842362125150586502933 4559383235724616433742325)
                ·
                  refine ⟨427442178349182790663343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4559383235724616433742325 427442178349182790663343)
                  ·
                    rfl

theorem cell22_3745983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 6, 5].length) (baseStart_3745983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3745983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3745983 prefixEnd_3745983 := by exact prefixLift 3745983
  have htrace : WordTrace (prefixWord ++ tailWord_3745983) baseStart_3745983 baseEnd_3745983 := by
    simpa [prefixWord, tailWord_3745983, baseEnd_3745983] using wordTrace_append hprefix tailTrace_3745983
  have hstable : (prefixWord ++ tailWord_3745983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745983).length < 2 ^ (prefixWord ++ tailWord_3745983).sum := by decide
  have hdescent : baseEnd_3745983 < baseStart_3745983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746060 : List Nat := [2, 2, 1, 2, 2, 2, 4, 1, 1, 5]
def baseStart_3746060 : Nat := 118140960795 + 3746060 * 2 ^ 59
def prefixEnd_3746060 : Nat := 4983230072969 + 3 ^ 40 * 3746060 * 2
def baseEnd_3746060 : Nat := 1282352893721145837814793

theorem tailTrace_3746060 : CollatzResearch.WordTrace tailWord_3746060 prefixEnd_3746060 1282352893721145837814793 := by
  unfold tailWord_3746060
  simp only [CollatzResearch.WordTrace]
  refine ⟨68315016404335935478965817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91086688539114580638621089 68315016404335935478965817)
  ·
    refine ⟨51236262303251951609224363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68315016404335935478965817 51236262303251951609224363)
    ·
      refine ⟨76854393454877927413836545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51236262303251951609224363 76854393454877927413836545)
      ·
        refine ⟨57640795091158445560377409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76854393454877927413836545 57640795091158445560377409)
        ·
          refine ⟨43230596318368834170283057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57640795091158445560377409 43230596318368834170283057)
          ·
            refine ⟨32422947238776625627712293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43230596318368834170283057 32422947238776625627712293)
            ·
              refine ⟨6079302607270617305196055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32422947238776625627712293 6079302607270617305196055)
              ·
                refine ⟨9118953910905925957794083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6079302607270617305196055 9118953910905925957794083)
                ·
                  refine ⟨13678430866358888936691125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9118953910905925957794083 13678430866358888936691125)
                  ·
                    refine ⟨1282352893721145837814793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13678430866358888936691125 1282352893721145837814793)
                    ·
                      rfl

theorem cell22_3746060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 1, 1, 5].length) (baseStart_3746060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3746060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3746060 prefixEnd_3746060 := by exact prefixLift 3746060
  have htrace : WordTrace (prefixWord ++ tailWord_3746060) baseStart_3746060 baseEnd_3746060 := by
    simpa [prefixWord, tailWord_3746060, baseEnd_3746060] using wordTrace_append hprefix tailTrace_3746060
  have hstable : (prefixWord ++ tailWord_3746060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746060).length < 2 ^ (prefixWord ++ tailWord_3746060).sum := by decide
  have hdescent : baseEnd_3746060 < baseStart_3746060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746075 : List Nat := [1, 1, 1, 1, 1, 1, 9, 1, 2, 4]
def baseStart_3746075 : Nat := 118140960795 + 3746075 * 2 ^ 59
def prefixEnd_3746075 : Nat := 4983230072969 + 3 ^ 40 * 3746075 * 2
def baseEnd_3746075 : Nat := 1282358028527690798689747

theorem tailTrace_3746075 : CollatzResearch.WordTrace tailWord_3746075 prefixEnd_3746075 1282358028527690798689747 := by
  unfold tailWord_3746075
  simp only [CollatzResearch.WordTrace]
  refine ⟨136630579903617528519727679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91087053269078352346485119 136630579903617528519727679)
  ·
    refine ⟨204945869855426292779591519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136630579903617528519727679 204945869855426292779591519)
    ·
      refine ⟨307418804783139439169387279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204945869855426292779591519 307418804783139439169387279)
      ·
        refine ⟨461128207174709158754080919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307418804783139439169387279 461128207174709158754080919)
        ·
          refine ⟨691692310762063738131121379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 461128207174709158754080919 691692310762063738131121379)
          ·
            refine ⟨1037538466143095607196682069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 691692310762063738131121379 1037538466143095607196682069)
            ·
              refine ⟨6079326950057200823418059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1037538466143095607196682069 6079326950057200823418059)
              ·
                refine ⟨9118990425085801235127089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6079326950057200823418059 9118990425085801235127089)
                ·
                  refine ⟨6839242818814350926345317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9118990425085801235127089 6839242818814350926345317)
                  ·
                    refine ⟨1282358028527690798689747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6839242818814350926345317 1282358028527690798689747)
                    ·
                      rfl

theorem cell22_3746075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 1, 2, 4].length) (baseStart_3746075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3746075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3746075 prefixEnd_3746075 := by exact prefixLift 3746075
  have htrace : WordTrace (prefixWord ++ tailWord_3746075) baseStart_3746075 baseEnd_3746075 := by
    simpa [prefixWord, tailWord_3746075, baseEnd_3746075] using wordTrace_append hprefix tailTrace_3746075
  have hstable : (prefixWord ++ tailWord_3746075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746075).length < 2 ^ (prefixWord ++ tailWord_3746075).sum := by decide
  have hdescent : baseEnd_3746075 < baseStart_3746075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746103 : List Nat := [1, 1, 3, 1, 2, 1, 1, 3, 1, 8]
def baseStart_3746103 : Nat := 118140960795 + 3746103 * 2 ^ 59
def prefixEnd_3746103 : Nat := 4983230072969 + 3 ^ 40 * 3746103 * 2
def baseEnd_3746103 : Nat := 1282367613499908058989661

theorem tailTrace_3746103 : CollatzResearch.WordTrace tailWord_3746103 prefixEnd_3746103 1282367613499908058989661 := by
  unfold tailWord_3746103
  simp only [CollatzResearch.WordTrace]
  refine ⟨136631601147516089301746963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91087734098344059534497975 136631601147516089301746963)
  ·
    refine ⟨204947401721274133952620445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136631601147516089301746963 204947401721274133952620445)
    ·
      refine ⟨76855275645477800232232667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204947401721274133952620445 76855275645477800232232667)
      ·
        refine ⟨115282913468216700348349001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76855275645477800232232667 115282913468216700348349001)
        ·
          refine ⟨86462185101162525261261751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115282913468216700348349001 86462185101162525261261751)
          ·
            refine ⟨129693277651743787891892627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86462185101162525261261751 129693277651743787891892627)
            ·
              refine ⟨194539916477615681837838941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129693277651743787891892627 194539916477615681837838941)
              ·
                refine ⟨72952468679105880689189603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 194539916477615681837838941 72952468679105880689189603)
                ·
                  refine ⟨109428703018658821033784405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72952468679105880689189603 109428703018658821033784405)
                  ·
                    refine ⟨1282367613499908058989661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 109428703018658821033784405 1282367613499908058989661)
                    ·
                      rfl

theorem cell22_3746103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 8].length) (baseStart_3746103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3746103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3746103 prefixEnd_3746103 := by exact prefixLift 3746103
  have htrace : WordTrace (prefixWord ++ tailWord_3746103) baseStart_3746103 baseEnd_3746103 := by
    simpa [prefixWord, tailWord_3746103, baseEnd_3746103] using wordTrace_append hprefix tailTrace_3746103
  have hstable : (prefixWord ++ tailWord_3746103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746103).length < 2 ^ (prefixWord ++ tailWord_3746103).sum := by decide
  have hdescent : baseEnd_3746103 < baseStart_3746103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746156 : List Nat := [2, 2, 1, 1, 7, 1, 1, 1, 3, 3]
def baseStart_3746156 : Nat := 118140960795 + 3746156 * 2 ^ 59
def prefixEnd_3746156 : Nat := 4983230072969 + 3 ^ 40 * 3746156 * 2
def baseEnd_3746156 : Nat := 1282385756483033587414499

theorem tailTrace_3746156 : CollatzResearch.WordTrace tailWord_3746156 prefixEnd_3746156 1282385756483033587414499 := by
  unfold tailWord_3746156
  simp only [CollatzResearch.WordTrace]
  refine ⟨68316767108162039676713161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91089022810882719568950881 68316767108162039676713161)
  ·
    refine ⟨51237575331121529757534871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68316767108162039676713161 51237575331121529757534871)
    ·
      refine ⟨76856362996682294636302307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51237575331121529757534871 76856362996682294636302307)
      ·
        refine ⟨115284544495023441954453461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76856362996682294636302307 115284544495023441954453461)
        ·
          refine ⟨2701981511602111920807503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 115284544495023441954453461 2701981511602111920807503)
          ·
            refine ⟨4052972267403167881211255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2701981511602111920807503 4052972267403167881211255)
            ·
              refine ⟨6079458401104751821816883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4052972267403167881211255 6079458401104751821816883)
              ·
                refine ⟨9119187601657127732725325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6079458401104751821816883 9119187601657127732725325)
                ·
                  refine ⟨3419695350621422899771997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9119187601657127732725325 3419695350621422899771997)
                  ·
                    refine ⟨1282385756483033587414499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3419695350621422899771997 1282385756483033587414499)
                    ·
                      rfl

theorem cell22_3746156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 1, 3, 3].length) (baseStart_3746156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3746156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3746156 prefixEnd_3746156 := by exact prefixLift 3746156
  have htrace : WordTrace (prefixWord ++ tailWord_3746156) baseStart_3746156 baseEnd_3746156 := by
    simpa [prefixWord, tailWord_3746156, baseEnd_3746156] using wordTrace_append hprefix tailTrace_3746156
  have hstable : (prefixWord ++ tailWord_3746156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746156).length < 2 ^ (prefixWord ++ tailWord_3746156).sum := by decide
  have hdescent : baseEnd_3746156 < baseStart_3746156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746180 : List Nat := [2, 3, 2, 1, 1, 2, 2, 1, 8]
def baseStart_3746180 : Nat := 118140960795 + 3746180 * 2 ^ 59
def prefixEnd_3746180 : Nat := 4983230072969 + 3 ^ 40 * 3746180 * 2
def baseEnd_3746180 : Nat := 427464657391168508271475

theorem tailTrace_3746180 : CollatzResearch.WordTrace tailWord_3746180 prefixEnd_3746180 427464657391168508271475 := by
  unfold tailWord_3746180
  simp only [CollatzResearch.WordTrace]
  refine ⟨68317204784118565726149997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91089606378824754301533329 68317204784118565726149997)
  ·
    refine ⟨25618951794044462147306249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68317204784118565726149997 25618951794044462147306249)
    ·
      refine ⟨19214213845533346610479687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25618951794044462147306249 19214213845533346610479687)
      ·
        refine ⟨28821320768300019915719531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19214213845533346610479687 28821320768300019915719531)
        ·
          refine ⟨43231981152450029873579297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28821320768300019915719531 43231981152450029873579297)
          ·
            refine ⟨32423985864337522405184473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43231981152450029873579297 32423985864337522405184473)
            ·
              refine ⟨24317989398253141803888355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32423985864337522405184473 24317989398253141803888355)
              ·
                refine ⟨36476984097379712705832533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24317989398253141803888355 36476984097379712705832533)
                ·
                  refine ⟨427464657391168508271475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36476984097379712705832533 427464657391168508271475)
                  ·
                    rfl

theorem cell22_3746180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 8].length) (baseStart_3746180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3746180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3746180 prefixEnd_3746180 := by exact prefixLift 3746180
  have htrace : WordTrace (prefixWord ++ tailWord_3746180) baseStart_3746180 baseEnd_3746180 := by
    simpa [prefixWord, tailWord_3746180, baseEnd_3746180] using wordTrace_append hprefix tailTrace_3746180
  have hstable : (prefixWord ++ tailWord_3746180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746180).length < 2 ^ (prefixWord ++ tailWord_3746180).sum := by decide
  have hdescent : baseEnd_3746180 < baseStart_3746180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746197 : List Nat := [1, 3, 2, 1, 1, 2, 1, 7, 4]
def baseStart_3746197 : Nat := 118140960795 + 3746197 * 2 ^ 59
def prefixEnd_3746197 : Nat := 4983230072969 + 3 ^ 40 * 3746197 * 2
def baseEnd_3746197 : Nat := 427466597206974382379791

theorem tailTrace_3746197 : CollatzResearch.WordTrace tailWord_3746197 prefixEnd_3746197 427466597206974382379791 := by
  unfold tailWord_3746197
  simp only [CollatzResearch.WordTrace]
  refine ⟨136635029609175543355668845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91090019739450362237112563 136635029609175543355668845)
  ·
    refine ⟨51238136103440828758375817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136635029609175543355668845 51238136103440828758375817)
    ·
      refine ⟨38428602077580621568781863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51238136103440828758375817 38428602077580621568781863)
      ·
        refine ⟨57642903116370932353172795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38428602077580621568781863 57642903116370932353172795)
        ·
          refine ⟨86464354674556398529759193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57642903116370932353172795 86464354674556398529759193)
          ·
            refine ⟨64848266005917298897319395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86464354674556398529759193 64848266005917298897319395)
            ·
              refine ⟨97272399008875948345979093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64848266005917298897319395 97272399008875948345979093)
              ·
                refine ⟨2279821851770530039358885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 97272399008875948345979093 2279821851770530039358885)
                ·
                  refine ⟨427466597206974382379791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2279821851770530039358885 427466597206974382379791)
                  ·
                    rfl

theorem cell22_3746197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 7, 4].length) (baseStart_3746197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3746197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3746197 prefixEnd_3746197 := by exact prefixLift 3746197
  have htrace : WordTrace (prefixWord ++ tailWord_3746197) baseStart_3746197 baseEnd_3746197 := by
    simpa [prefixWord, tailWord_3746197, baseEnd_3746197] using wordTrace_append hprefix tailTrace_3746197
  have hstable : (prefixWord ++ tailWord_3746197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746197).length < 2 ^ (prefixWord ++ tailWord_3746197).sum := by decide
  have hdescent : baseEnd_3746197 < baseStart_3746197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746212 : List Nat := [2, 3, 1, 2, 1, 1, 2, 3, 4, 3]
def baseStart_3746212 : Nat := 118140960795 + 3746212 * 2 ^ 59
def prefixEnd_3746212 : Nat := 4983230072969 + 3 ^ 40 * 3746212 * 2
def baseEnd_3746212 : Nat := 1282404926427468108014327

theorem tailTrace_3746212 : CollatzResearch.WordTrace tailWord_3746212 prefixEnd_3746212 1282404926427468108014327 := by
  unfold tailWord_3746212
  simp only [CollatzResearch.WordTrace]
  refine ⟨68317788352060600458732445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91090384469414133944976593 68317788352060600458732445)
  ·
    refine ⟨25619170632022725172024667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68317788352060600458732445 25619170632022725172024667)
    ·
      refine ⟨38428755948034087758037001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25619170632022725172024667 38428755948034087758037001)
      ·
        refine ⟨28821566961025565818527751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38428755948034087758037001 28821566961025565818527751)
        ·
          refine ⟨43232350441538348727791627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28821566961025565818527751 43232350441538348727791627)
          ·
            refine ⟨64848525662307523091687441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43232350441538348727791627 64848525662307523091687441)
            ·
              refine ⟨48636394246730642318765581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64848525662307523091687441 48636394246730642318765581)
              ·
                refine ⟨18238647842523990869537093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48636394246730642318765581 18238647842523990869537093)
                ·
                  refine ⟨3419746470473248288038205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18238647842523990869537093 3419746470473248288038205)
                  ·
                    refine ⟨1282404926427468108014327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3419746470473248288038205 1282404926427468108014327)
                    ·
                      rfl

theorem cell22_3746212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 4, 3].length) (baseStart_3746212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3746212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3746212 prefixEnd_3746212 := by exact prefixLift 3746212
  have htrace : WordTrace (prefixWord ++ tailWord_3746212) baseStart_3746212 baseEnd_3746212 := by
    simpa [prefixWord, tailWord_3746212, baseEnd_3746212] using wordTrace_append hprefix tailTrace_3746212
  have hstable : (prefixWord ++ tailWord_3746212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746212).length < 2 ^ (prefixWord ++ tailWord_3746212).sum := by decide
  have hdescent : baseEnd_3746212 < baseStart_3746212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746229 : List Nat := [1, 3, 3, 2, 3, 1, 2, 1, 1, 5]
def baseStart_3746229 : Nat := 118140960795 + 3746229 * 2 ^ 59
def prefixEnd_3746229 : Nat := 4983230072969 + 3 ^ 40 * 3746229 * 2
def baseEnd_3746229 : Nat := 1282410745874885730339275

theorem tailTrace_3746229 : CollatzResearch.WordTrace tailWord_3746229 prefixEnd_3746229 1282410745874885730339275 := by
  unfold tailWord_3746229
  simp only [CollatzResearch.WordTrace]
  refine ⟨136636196745059612820833741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91090797830039741880555827 136636196745059612820833741)
  ·
    refine ⟨51238573779397354807812653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136636196745059612820833741 51238573779397354807812653)
    ·
      refine ⟨19214465167274008052929745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51238573779397354807812653 19214465167274008052929745)
      ·
        refine ⟨14410848875455506039697309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19214465167274008052929745 14410848875455506039697309)
        ·
          refine ⟨5404068328295814764886491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14410848875455506039697309 5404068328295814764886491)
          ·
            refine ⟨8106102492443722147329737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5404068328295814764886491 8106102492443722147329737)
            ·
              refine ⟨6079576869332791610497303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8106102492443722147329737 6079576869332791610497303)
              ·
                refine ⟨9119365303999187415745955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6079576869332791610497303 9119365303999187415745955)
                ·
                  refine ⟨13679047955998781123618933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9119365303999187415745955 13679047955998781123618933)
                  ·
                    refine ⟨1282410745874885730339275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13679047955998781123618933 1282410745874885730339275)
                    ·
                      rfl

theorem cell22_3746229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_3746229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3746229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3746229 prefixEnd_3746229 := by exact prefixLift 3746229
  have htrace : WordTrace (prefixWord ++ tailWord_3746229) baseStart_3746229 baseEnd_3746229 := by
    simpa [prefixWord, tailWord_3746229, baseEnd_3746229] using wordTrace_append hprefix tailTrace_3746229
  have hstable : (prefixWord ++ tailWord_3746229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746229).length < 2 ^ (prefixWord ++ tailWord_3746229).sum := by decide
  have hdescent : baseEnd_3746229 < baseStart_3746229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746244 : List Nat := [2, 3, 3, 2, 2, 1, 1, 1, 1, 6]
def baseStart_3746244 : Nat := 118140960795 + 3746244 * 2 ^ 59
def prefixEnd_3746244 : Nat := 4983230072969 + 3 ^ 40 * 3746244 * 2
def baseEnd_3746244 : Nat := 1282415880681430691214229

theorem tailTrace_3746244 : CollatzResearch.WordTrace tailWord_3746244 prefixEnd_3746244 1282415880681430691214229 := by
  unfold tailWord_3746244
  simp only [CollatzResearch.WordTrace]
  refine ⟨68318371920002635191314893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91091162560003513588419857 68318371920002635191314893)
  ·
    refine ⟨25619389470000988196743085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68318371920002635191314893 25619389470000988196743085)
    ·
      refine ⟨9607271051250370573778657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25619389470000988196743085 9607271051250370573778657)
      ·
        refine ⟨7205453288437777930333993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9607271051250370573778657 7205453288437777930333993)
        ·
          refine ⟨5404089966328333447750495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7205453288437777930333993 5404089966328333447750495)
          ·
            refine ⟨8106134949492500171625743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5404089966328333447750495 8106134949492500171625743)
            ·
              refine ⟨12159202424238750257438615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8106134949492500171625743 12159202424238750257438615)
              ·
                refine ⟨18238803636358125386157923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12159202424238750257438615 18238803636358125386157923)
                ·
                  refine ⟨27358205454537188079236885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18238803636358125386157923 27358205454537188079236885)
                  ·
                    refine ⟨1282415880681430691214229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27358205454537188079236885 1282415880681430691214229)
                    ·
                      rfl

theorem cell22_3746244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_3746244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3746244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3746244 prefixEnd_3746244 := by exact prefixLift 3746244
  have htrace : WordTrace (prefixWord ++ tailWord_3746244) baseStart_3746244 baseEnd_3746244 := by
    simpa [prefixWord, tailWord_3746244, baseEnd_3746244] using wordTrace_append hprefix tailTrace_3746244
  have hstable : (prefixWord ++ tailWord_3746244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746244).length < 2 ^ (prefixWord ++ tailWord_3746244).sum := by decide
  have hdescent : baseEnd_3746244 < baseStart_3746244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746293 : List Nat := [1, 3, 5, 1, 3, 1, 2, 6]
def baseStart_3746293 : Nat := 118140960795 + 3746293 * 2 ^ 59
def prefixEnd_3746293 : Nat := 4983230072969 + 3 ^ 40 * 3746293 * 2
def baseEnd_3746293 : Nat := 142492517153645655193231

theorem tailTrace_3746293 : CollatzResearch.WordTrace tailWord_3746293 prefixEnd_3746293 142492517153645655193231 := by
  unfold tailWord_3746293
  simp only [CollatzResearch.WordTrace]
  refine ⟨136638531016827751751163533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91092354011218501167442355 136638531016827751751163533)
  ·
    refine ⟨51239449131310406906686325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136638531016827751751163533 51239449131310406906686325)
    ·
      refine ⟨4803698356060350647501843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51239449131310406906686325 4803698356060350647501843)
      ·
        refine ⟨7205547534090525971252765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4803698356060350647501843 7205547534090525971252765)
        ·
          refine ⟨2702080325283947239219787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7205547534090525971252765 2702080325283947239219787)
          ·
            refine ⟨4053120487925920858829681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2702080325283947239219787 4053120487925920858829681)
            ·
              refine ⟨3039840365944440644122261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4053120487925920858829681 3039840365944440644122261)
              ·
                refine ⟨142492517153645655193231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3039840365944440644122261 142492517153645655193231)
                ·
                  rfl

theorem cell22_3746293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 2, 6].length) (baseStart_3746293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3746293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3746293 prefixEnd_3746293 := by exact prefixLift 3746293
  have htrace : WordTrace (prefixWord ++ tailWord_3746293) baseStart_3746293 baseEnd_3746293 := by
    simpa [prefixWord, tailWord_3746293, baseEnd_3746293] using wordTrace_append hprefix tailTrace_3746293
  have hstable : (prefixWord ++ tailWord_3746293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746293).length < 2 ^ (prefixWord ++ tailWord_3746293).sum := by decide
  have hdescent : baseEnd_3746293 < baseStart_3746293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746308 : List Nat := [2, 3, 2, 3, 1, 1, 3, 3, 1, 3]
def baseStart_3746308 : Nat := 118140960795 + 3746308 * 2 ^ 59
def prefixEnd_3746308 : Nat := 4983230072969 + 3 ^ 40 * 3746308 * 2
def baseEnd_3746308 : Nat := 1282437789189355857614033

theorem tailTrace_3746308 : CollatzResearch.WordTrace tailWord_3746308 prefixEnd_3746308 1282437789189355857614033 := by
  unfold tailWord_3746308
  simp only [CollatzResearch.WordTrace]
  refine ⟨68319539055886704656479789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91092718741182272875306385 68319539055886704656479789)
  ·
    refine ⟨25619827145957514246179921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68319539055886704656479789 25619827145957514246179921)
    ·
      refine ⟨19214870359468135684634941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25619827145957514246179921 19214870359468135684634941)
      ·
        refine ⟨7205576384800550881738103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19214870359468135684634941 7205576384800550881738103)
        ·
          refine ⟨10808364577200826322607155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7205576384800550881738103 10808364577200826322607155)
          ·
            refine ⟨16212546865801239483910733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10808364577200826322607155 16212546865801239483910733)
            ·
              refine ⟨6079705074675464806466525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16212546865801239483910733 6079705074675464806466525)
              ·
                refine ⟨2279889403003299302424947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6079705074675464806466525 2279889403003299302424947)
                ·
                  refine ⟨3419834104504948953637421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2279889403003299302424947 3419834104504948953637421)
                  ·
                    refine ⟨1282437789189355857614033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3419834104504948953637421 1282437789189355857614033)
                    ·
                      rfl

theorem cell22_3746308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 3, 1, 3].length) (baseStart_3746308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3746308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3746308 prefixEnd_3746308 := by exact prefixLift 3746308
  have htrace : WordTrace (prefixWord ++ tailWord_3746308) baseStart_3746308 baseEnd_3746308 := by
    simpa [prefixWord, tailWord_3746308, baseEnd_3746308] using wordTrace_append hprefix tailTrace_3746308
  have hstable : (prefixWord ++ tailWord_3746308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746308).length < 2 ^ (prefixWord ++ tailWord_3746308).sum := by decide
  have hdescent : baseEnd_3746308 < baseStart_3746308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746364 : List Nat := [2, 2, 2, 2, 3, 2, 1, 2, 1, 5]
def baseStart_3746364 : Nat := 118140960795 + 3746364 * 2 ^ 59
def prefixEnd_3746364 : Nat := 4983230072969 + 3 ^ 40 * 3746364 * 2
def baseEnd_3746364 : Nat := 1282456959133790378213861

theorem tailTrace_3746364 : CollatzResearch.WordTrace tailWord_3746364 prefixEnd_3746364 1282456959133790378213861 := by
  unfold tailWord_3746364
  simp only [CollatzResearch.WordTrace]
  refine ⟨68320560299785265438499073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91094080399713687251332097 68320560299785265438499073)
  ·
    refine ⟨51240420224838949078874305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68320560299785265438499073 51240420224838949078874305)
    ·
      refine ⟨38430315168629211809155729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51240420224838949078874305 38430315168629211809155729)
      ·
        refine ⟨28822736376471908856866797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38430315168629211809155729 28822736376471908856866797)
        ·
          refine ⟨10808526141176965821325049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28822736376471908856866797 10808526141176965821325049)
          ·
            refine ⟨8106394605882724365993787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10808526141176965821325049 8106394605882724365993787)
            ·
              refine ⟨12159591908824086548990681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8106394605882724365993787 12159591908824086548990681)
              ·
                refine ⟨9119693931618064911743011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12159591908824086548990681 9119693931618064911743011)
                ·
                  refine ⟨13679540897427097367614517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9119693931618064911743011 13679540897427097367614517)
                  ·
                    refine ⟨1282456959133790378213861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13679540897427097367614517 1282456959133790378213861)
                    ·
                      rfl

theorem cell22_3746364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 2, 1, 5].length) (baseStart_3746364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3746364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3746364 prefixEnd_3746364 := by exact prefixLift 3746364
  have htrace : WordTrace (prefixWord ++ tailWord_3746364) baseStart_3746364 baseEnd_3746364 := by
    simpa [prefixWord, tailWord_3746364, baseEnd_3746364] using wordTrace_append hprefix tailTrace_3746364
  have hstable : (prefixWord ++ tailWord_3746364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746364).length < 2 ^ (prefixWord ++ tailWord_3746364).sum := by decide
  have hdescent : baseEnd_3746364 < baseStart_3746364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746407 : List Nat := [1, 1, 5, 1, 1, 1, 1, 1, 4, 6]
def baseStart_3746407 : Nat := 118140960795 + 3746407 * 2 ^ 59
def prefixEnd_3746407 : Nat := 4983230072969 + 3 ^ 40 * 3746407 * 2
def baseEnd_3746407 : Nat := 1282471678912552599388729

theorem tailTrace_3746407 : CollatzResearch.WordTrace tailWord_3746407 prefixEnd_3746407 1282471678912552599388729 := by
  unfold tailWord_3746407
  simp only [CollatzResearch.WordTrace]
  refine ⟨136642688938414749220813475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91095125958943166147208983 136642688938414749220813475)
  ·
    refine ⟨204964033407622123831220213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136642688938414749220813475 204964033407622123831220213)
    ·
      refine ⟨19215378131964574109176895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 204964033407622123831220213 19215378131964574109176895)
      ·
        refine ⟨28823067197946861163765343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19215378131964574109176895 28823067197946861163765343)
        ·
          refine ⟨43234600796920291745648015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28823067197946861163765343 43234600796920291745648015)
          ·
            refine ⟨64851901195380437618472023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43234600796920291745648015 64851901195380437618472023)
            ·
              refine ⟨97277851793070656427708035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64851901195380437618472023 97277851793070656427708035)
              ·
                refine ⟨145916777689605984641562053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97277851793070656427708035 145916777689605984641562053)
                ·
                  refine ⟨27359395816801122120292885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 145916777689605984641562053 27359395816801122120292885)
                  ·
                    refine ⟨1282471678912552599388729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27359395816801122120292885 1282471678912552599388729)
                    ·
                      rfl

theorem cell22_3746407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_3746407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3746407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3746407 prefixEnd_3746407 := by exact prefixLift 3746407
  have htrace : WordTrace (prefixWord ++ tailWord_3746407) baseStart_3746407 baseEnd_3746407 := by
    simpa [prefixWord, tailWord_3746407, baseEnd_3746407] using wordTrace_append hprefix tailTrace_3746407
  have hstable : (prefixWord ++ tailWord_3746407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746407).length < 2 ^ (prefixWord ++ tailWord_3746407).sum := by decide
  have hdescent : baseEnd_3746407 < baseStart_3746407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746456 : List Nat := [2, 1, 2, 4, 1, 1, 5, 1, 5]
def baseStart_3746456 : Nat := 118140960795 + 3746456 * 2 ^ 59
def prefixEnd_3746456 : Nat := 4983230072969 + 3 ^ 40 * 3746456 * 2
def baseEnd_3746456 : Nat := 427496150871310934971193

theorem tailTrace_3746456 : CollatzResearch.WordTrace tailWord_3746456 prefixEnd_3746456 427496150871310934971193 := by
  unfold tailWord_3746456
  simp only [CollatzResearch.WordTrace]
  refine ⟨68322238057618615294673611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91096317410158153726231481 68322238057618615294673611)
  ·
    refine ⟨102483357086427922942010417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68322238057618615294673611 102483357086427922942010417)
    ·
      refine ⟨76862517814820942206507813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102483357086427922942010417 76862517814820942206507813)
      ·
        refine ⟨14411722090278926663720215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76862517814820942206507813 14411722090278926663720215)
        ·
          refine ⟨21617583135418389995580323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14411722090278926663720215 21617583135418389995580323)
          ·
            refine ⟨32426374703127584993370485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21617583135418389995580323 32426374703127584993370485)
            ·
              refine ⟨3039972628418211093128483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32426374703127584993370485 3039972628418211093128483)
              ·
                refine ⟨4559958942627316639692725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3039972628418211093128483 4559958942627316639692725)
                ·
                  refine ⟨427496150871310934971193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4559958942627316639692725 427496150871310934971193)
                  ·
                    rfl

theorem cell22_3746456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 5, 1, 5].length) (baseStart_3746456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3746456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3746456 prefixEnd_3746456 := by exact prefixLift 3746456
  have htrace : WordTrace (prefixWord ++ tailWord_3746456) baseStart_3746456 baseEnd_3746456 := by
    simpa [prefixWord, tailWord_3746456, baseEnd_3746456] using wordTrace_append hprefix tailTrace_3746456
  have hstable : (prefixWord ++ tailWord_3746456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746456).length < 2 ^ (prefixWord ++ tailWord_3746456).sum := by decide
  have hdescent : baseEnd_3746456 < baseStart_3746456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746467 : List Nat := [1, 1, 1, 4, 1, 1, 2, 3, 8]
def baseStart_3746467 : Nat := 118140960795 + 3746467 * 2 ^ 59
def prefixEnd_3746467 : Nat := 4983230072969 + 3 ^ 40 * 3746467 * 2
def baseEnd_3746467 : Nat := 427497406046244147629515

theorem tailTrace_3746467 : CollatzResearch.WordTrace tailWord_3746467 prefixEnd_3746467 427497406046244147629515 := by
  unfold tailWord_3746467
  simp only [CollatzResearch.WordTrace]
  refine ⟨136644877318197379467997655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91096584878798252978665103 136644877318197379467997655)
  ·
    refine ⟨204967315977296069201996483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136644877318197379467997655 204967315977296069201996483)
    ·
      refine ⟨307450973965944103802994725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204967315977296069201996483 307450973965944103802994725)
      ·
        refine ⟨57647057618614519463061511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 307450973965944103802994725 57647057618614519463061511)
        ·
          refine ⟨86470586427921779194592267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57647057618614519463061511 86470586427921779194592267)
          ·
            refine ⟨129705879641882668791888401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86470586427921779194592267 129705879641882668791888401)
            ·
              refine ⟨97279409731412001593916301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129705879641882668791888401 97279409731412001593916301)
              ·
                refine ⟨36479778649279500597718613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97279409731412001593916301 36479778649279500597718613)
                ·
                  refine ⟨427497406046244147629515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36479778649279500597718613 427497406046244147629515)
                  ·
                    rfl

theorem cell22_3746467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 8].length) (baseStart_3746467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3746467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3746467 prefixEnd_3746467 := by exact prefixLift 3746467
  have htrace : WordTrace (prefixWord ++ tailWord_3746467) baseStart_3746467 baseEnd_3746467 := by
    simpa [prefixWord, tailWord_3746467, baseEnd_3746467] using wordTrace_append hprefix tailTrace_3746467
  have hstable : (prefixWord ++ tailWord_3746467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746467).length < 2 ^ (prefixWord ++ tailWord_3746467).sum := by decide
  have hdescent : baseEnd_3746467 < baseStart_3746467 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746529 : List Nat := [1, 2, 3, 1, 4, 1, 2, 8]
def baseStart_3746529 : Nat := 118140960795 + 3746529 * 2 ^ 59
def prefixEnd_3746529 : Nat := 4983230072969 + 3 ^ 40 * 3746529 * 2
def baseEnd_3746529 : Nat := 142501493556198327537595

theorem tailTrace_3746529 : CollatzResearch.WordTrace tailWord_3746529 prefixEnd_3746529 142501493556198327537595 := by
  unfold tailWord_3746529
  simp only [CollatzResearch.WordTrace]
  refine ⟨136647138643972764056754641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91098092429315176037836427 136647138643972764056754641)
  ·
    refine ⟨102485353982979573042565981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136647138643972764056754641 102485353982979573042565981)
    ·
      refine ⟨38432007743617339890962243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102485353982979573042565981 38432007743617339890962243)
      ·
        refine ⟨57648011615426009836443365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38432007743617339890962243 57648011615426009836443365)
        ·
          refine ⟨10809002177892376844333131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57648011615426009836443365 10809002177892376844333131)
          ·
            refine ⟨16213503266838565266499697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10809002177892376844333131 16213503266838565266499697)
            ·
              refine ⟨12160127450128923949874773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16213503266838565266499697 12160127450128923949874773)
              ·
                refine ⟨142501493556198327537595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12160127450128923949874773 142501493556198327537595)
                ·
                  rfl

theorem cell22_3746529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 8].length) (baseStart_3746529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3746529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3746529 prefixEnd_3746529 := by exact prefixLift 3746529
  have htrace : WordTrace (prefixWord ++ tailWord_3746529) baseStart_3746529 baseEnd_3746529 := by
    simpa [prefixWord, tailWord_3746529, baseEnd_3746529] using wordTrace_append hprefix tailTrace_3746529
  have hstable : (prefixWord ++ tailWord_3746529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746529).length < 2 ^ (prefixWord ++ tailWord_3746529).sum := by decide
  have hdescent : baseEnd_3746529 < baseStart_3746529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746531 : List Nat := [1, 1, 1, 7, 1, 1, 1, 3, 2, 4]
def baseStart_3746531 : Nat := 118140960795 + 3746531 * 2 ^ 59
def prefixEnd_3746531 : Nat := 4983230072969 + 3 ^ 40 * 3746531 * 2
def baseEnd_3746531 : Nat := 1282514126646657609288349

theorem tailTrace_3746531 : CollatzResearch.WordTrace tailWord_3746531 prefixEnd_3746531 1282514126646657609288349 := by
  unfold tailWord_3746531
  simp only [CollatzResearch.WordTrace]
  refine ⟨136647211589965518398327447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91098141059977012265551631 136647211589965518398327447)
  ·
    refine ⟨204970817384948277597491171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136647211589965518398327447 204970817384948277597491171)
    ·
      refine ⟨307456226077422416396236757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204970817384948277597491171 307456226077422416396236757)
      ·
        refine ⟨7206005298689587884286799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 307456226077422416396236757 7206005298689587884286799)
        ·
          refine ⟨10809007948034381826430199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7206005298689587884286799 10809007948034381826430199)
          ·
            refine ⟨16213511922051572739645299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10809007948034381826430199 16213511922051572739645299)
            ·
              refine ⟨24320267883077359109467949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16213511922051572739645299 24320267883077359109467949)
              ·
                refine ⟨9120100456154009666050481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24320267883077359109467949 9120100456154009666050481)
                ·
                  refine ⟨6840075342115507249537861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9120100456154009666050481 6840075342115507249537861)
                  ·
                    refine ⟨1282514126646657609288349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6840075342115507249537861 1282514126646657609288349)
                    ·
                      rfl

theorem cell22_3746531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 3, 2, 4].length) (baseStart_3746531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3746531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3746531 prefixEnd_3746531 := by exact prefixLift 3746531
  have htrace : WordTrace (prefixWord ++ tailWord_3746531) baseStart_3746531 baseEnd_3746531 := by
    simpa [prefixWord, tailWord_3746531, baseEnd_3746531] using wordTrace_append hprefix tailTrace_3746531
  have hstable : (prefixWord ++ tailWord_3746531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746531).length < 2 ^ (prefixWord ++ tailWord_3746531).sum := by decide
  have hdescent : baseEnd_3746531 < baseStart_3746531 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746561 : List Nat := [1, 2, 4, 1, 1, 1, 1, 5, 3, 3]
def baseStart_3746561 : Nat := 118140960795 + 3746561 * 2 ^ 59
def prefixEnd_3746561 : Nat := 4983230072969 + 3 ^ 40 * 3746561 * 2
def baseEnd_3746561 : Nat := 1282524396259747531038257

theorem tailTrace_3746561 : CollatzResearch.WordTrace tailWord_3746561 prefixEnd_3746561 1282524396259747531038257 := by
  unfold tailWord_3746561
  simp only [CollatzResearch.WordTrace]
  refine ⟨136648305779856833521919537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91098870519904555681279691 136648305779856833521919537)
  ·
    refine ⟨102486229334892625141439653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136648305779856833521919537 102486229334892625141439653)
    ·
      refine ⟨19216168000292367214019935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102486229334892625141439653 19216168000292367214019935)
      ·
        refine ⟨28824252000438550821029903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19216168000292367214019935 28824252000438550821029903)
        ·
          refine ⟨43236378000657826231544855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28824252000438550821029903 43236378000657826231544855)
          ·
            refine ⟨64854567000986739347317283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43236378000657826231544855 64854567000986739347317283)
            ·
              refine ⟨97281850501480109020975925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64854567000986739347317283 97281850501480109020975925)
              ·
                refine ⟨9120173484513760220716493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97281850501480109020975925 9120173484513760220716493)
                ·
                  refine ⟨3420065056692660082768685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9120173484513760220716493 3420065056692660082768685)
                  ·
                    refine ⟨1282524396259747531038257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3420065056692660082768685 1282524396259747531038257)
                    ·
                      rfl

theorem cell22_3746561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 5, 3, 3].length) (baseStart_3746561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3746561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3746561 prefixEnd_3746561 := by exact prefixLift 3746561
  have htrace : WordTrace (prefixWord ++ tailWord_3746561) baseStart_3746561 baseEnd_3746561 := by
    simpa [prefixWord, tailWord_3746561, baseEnd_3746561] using wordTrace_append hprefix tailTrace_3746561
  have hstable : (prefixWord ++ tailWord_3746561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746561).length < 2 ^ (prefixWord ++ tailWord_3746561).sum := by decide
  have hdescent : baseEnd_3746561 < baseStart_3746561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746574 : List Nat := [4, 1, 1, 2, 1, 1, 1, 2, 9]
def baseStart_3746574 : Nat := 118140960795 + 3746574 * 2 ^ 59
def prefixEnd_3746574 : Nat := 4983230072969 + 3 ^ 40 * 3746574 * 2
def baseEnd_3746574 : Nat := 427509615475139943487739

theorem tailTrace_3746574 : CollatzResearch.WordTrace tailWord_3746574 prefixEnd_3746574 427509615475139943487739 := by
  unfold tailWord_3746574
  simp only [CollatzResearch.WordTrace]
  refine ⟨17081097491101217092767847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91099186619206491161428517 17081097491101217092767847)
  ·
    refine ⟨25621646236651825639151771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17081097491101217092767847 25621646236651825639151771)
    ·
      refine ⟨38432469354977738458727657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25621646236651825639151771 38432469354977738458727657)
      ·
        refine ⟨28824352016233303844045743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38432469354977738458727657 28824352016233303844045743)
        ·
          refine ⟨43236528024349955766068615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28824352016233303844045743 43236528024349955766068615)
          ·
            refine ⟨64854792036524933649102923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43236528024349955766068615 64854792036524933649102923)
            ·
              refine ⟨97282188054787400473654385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64854792036524933649102923 97282188054787400473654385)
              ·
                refine ⟨72961641041090550355240789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97282188054787400473654385 72961641041090550355240789)
                ·
                  refine ⟨427509615475139943487739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 72961641041090550355240789 427509615475139943487739)
                  ·
                    rfl

theorem cell22_3746574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 9].length) (baseStart_3746574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3746574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3746574 prefixEnd_3746574 := by exact prefixLift 3746574
  have htrace : WordTrace (prefixWord ++ tailWord_3746574) baseStart_3746574 baseEnd_3746574 := by
    simpa [prefixWord, tailWord_3746574, baseEnd_3746574] using wordTrace_append hprefix tailTrace_3746574
  have hstable : (prefixWord ++ tailWord_3746574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746574).length < 2 ^ (prefixWord ++ tailWord_3746574).sum := by decide
  have hdescent : baseEnd_3746574 < baseStart_3746574 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746636 : List Nat := [2, 2, 1, 3, 3, 1, 2, 2, 6]
def baseStart_3746636 : Nat := 118140960795 + 3746636 * 2 ^ 59
def prefixEnd_3746636 : Nat := 4983230072969 + 3 ^ 40 * 3746636 * 2
def baseEnd_3746636 : Nat := 427516690097490778471009

theorem tailTrace_3746636 : CollatzResearch.WordTrace tailWord_3746636 prefixEnd_3746636 427516690097490778471009 := by
  unfold tailWord_3746636
  simp only [CollatzResearch.WordTrace]
  refine ⟨68325520627292560665449881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91100694169723414220599841 68325520627292560665449881)
  ·
    refine ⟨51244140470469420499087411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68325520627292560665449881 51244140470469420499087411)
    ·
      refine ⟨76866210705704130748631117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51244140470469420499087411 76866210705704130748631117)
      ·
        refine ⟨28824829014639049030736669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76866210705704130748631117 28824829014639049030736669)
        ·
          refine ⟨10809310880489643386526251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28824829014639049030736669 10809310880489643386526251)
          ·
            refine ⟨16213966320734465079789377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10809310880489643386526251 16213966320734465079789377)
            ·
              refine ⟨12160474740550848809842033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16213966320734465079789377 12160474740550848809842033)
              ·
                refine ⟨9120356055413136607381525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12160474740550848809842033 9120356055413136607381525)
                ·
                  refine ⟨427516690097490778471009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9120356055413136607381525 427516690097490778471009)
                  ·
                    rfl

theorem cell22_3746636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 2, 6].length) (baseStart_3746636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3746636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3746636 prefixEnd_3746636 := by exact prefixLift 3746636
  have htrace : WordTrace (prefixWord ++ tailWord_3746636) baseStart_3746636 baseEnd_3746636 := by
    simpa [prefixWord, tailWord_3746636, baseEnd_3746636] using wordTrace_append hprefix tailTrace_3746636
  have hstable : (prefixWord ++ tailWord_3746636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746636).length < 2 ^ (prefixWord ++ tailWord_3746636).sum := by decide
  have hdescent : baseEnd_3746636 < baseStart_3746636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746668 : List Nat := [2, 2, 1, 1, 4, 1, 2, 4, 2, 3]
def baseStart_3746668 : Nat := 118140960795 + 3746668 * 2 ^ 59
def prefixEnd_3746668 : Nat := 4983230072969 + 3 ^ 40 * 3746668 * 2
def baseEnd_3746668 : Nat := 1282561024546434918612929

theorem tailTrace_3746668 : CollatzResearch.WordTrace tailWord_3746668 prefixEnd_3746668 1282561024546434918612929 := by
  unfold tailWord_3746668
  simp only [CollatzResearch.WordTrace]
  refine ⟨68326104195234595398032329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91101472260312793864043105 68326104195234595398032329)
  ·
    refine ⟨51244578146425946548524247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68326104195234595398032329 51244578146425946548524247)
    ·
      refine ⟨76866867219638919822786371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51244578146425946548524247 76866867219638919822786371)
      ·
        refine ⟨115300300829458379734179557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76866867219638919822786371 115300300829458379734179557)
        ·
          refine ⟨21618806405523446200158667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115300300829458379734179557 21618806405523446200158667)
          ·
            refine ⟨32428209608285169300238001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21618806405523446200158667 32428209608285169300238001)
            ·
              refine ⟨24321157206213876975178501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32428209608285169300238001 24321157206213876975178501)
              ·
                refine ⟨4560216976165101932845969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24321157206213876975178501 4560216976165101932845969)
                ·
                  refine ⟨3420162732123826449634477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4560216976165101932845969 3420162732123826449634477)
                  ·
                    refine ⟨1282561024546434918612929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3420162732123826449634477 1282561024546434918612929)
                    ·
                      rfl

theorem cell22_3746668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 3].length) (baseStart_3746668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3746668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3746668 prefixEnd_3746668 := by exact prefixLift 3746668
  have htrace : WordTrace (prefixWord ++ tailWord_3746668) baseStart_3746668 baseEnd_3746668 := by
    simpa [prefixWord, tailWord_3746668, baseEnd_3746668] using wordTrace_append hprefix tailTrace_3746668
  have hstable : (prefixWord ++ tailWord_3746668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746668).length < 2 ^ (prefixWord ++ tailWord_3746668).sum := by decide
  have hdescent : baseEnd_3746668 < baseStart_3746668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746670 : List Nat := [4, 1, 2, 3, 2, 2, 1, 1, 6]
def baseStart_3746670 : Nat := 118140960795 + 3746670 * 2 ^ 59
def prefixEnd_3746670 : Nat := 4983230072969 + 3 ^ 40 * 3746670 * 2
def baseEnd_3746670 : Nat := 427520569729102526687641

theorem tailTrace_3746670 : CollatzResearch.WordTrace tailWord_3746670 prefixEnd_3746670 427520569729102526687641 := by
  unfold tailWord_3746670
  simp only [CollatzResearch.WordTrace]
  refine ⟨17081535167057743142204683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91101520890974630091758309 17081535167057743142204683)
  ·
    refine ⟨25622302750586614713307025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17081535167057743142204683 25622302750586614713307025)
    ·
      refine ⟨19216727062939961034980269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25622302750586614713307025 19216727062939961034980269)
      ·
        refine ⟨7206272648602485388117601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19216727062939961034980269 7206272648602485388117601)
        ·
          refine ⟨5404704486451864041088201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7206272648602485388117601 5404704486451864041088201)
          ·
            refine ⟨4053528364838898030816151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5404704486451864041088201 4053528364838898030816151)
            ·
              refine ⟨6080292547258347046224227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4053528364838898030816151 6080292547258347046224227)
              ·
                refine ⟨9120438820887520569336341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6080292547258347046224227 9120438820887520569336341)
                ·
                  refine ⟨427520569729102526687641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9120438820887520569336341 427520569729102526687641)
                  ·
                    rfl

theorem cell22_3746670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 1, 6].length) (baseStart_3746670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3746670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3746670 prefixEnd_3746670 := by exact prefixLift 3746670
  have htrace : WordTrace (prefixWord ++ tailWord_3746670) baseStart_3746670 baseEnd_3746670 := by
    simpa [prefixWord, tailWord_3746670, baseEnd_3746670] using wordTrace_append hprefix tailTrace_3746670
  have hstable : (prefixWord ++ tailWord_3746670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746670).length < 2 ^ (prefixWord ++ tailWord_3746670).sum := by decide
  have hdescent : baseEnd_3746670 < baseStart_3746670 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746681 : List Nat := [1, 2, 1, 3, 2, 4, 2, 7]
def baseStart_3746681 : Nat := 118140960795 + 3746681 * 2 ^ 59
def prefixEnd_3746681 : Nat := 4983230072969 + 3 ^ 40 * 3746681 * 2
def baseEnd_3746681 : Nat := 142507274968011913115321

theorem tailTrace_3746681 : CollatzResearch.WordTrace tailWord_3746681 prefixEnd_3746681 142507274968011913115321 := by
  unfold tailWord_3746681
  simp only [CollatzResearch.WordTrace]
  refine ⟨136652682539422094016287897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91101788359614729344191931 136652682539422094016287897)
  ·
    refine ⟨102489511904566570512215923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136652682539422094016287897 102489511904566570512215923)
    ·
      refine ⟨153734267856849855768323885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102489511904566570512215923 153734267856849855768323885)
      ·
        refine ⟨57650350446318695913121457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153734267856849855768323885 57650350446318695913121457)
        ·
          refine ⟨43237762834739021934841093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57650350446318695913121457 43237762834739021934841093)
          ·
            refine ⟨8107080531513566612782705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43237762834739021934841093 8107080531513566612782705)
            ·
              refine ⟨6080310398635174959587029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8107080531513566612782705 6080310398635174959587029)
              ·
                refine ⟨142507274968011913115321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6080310398635174959587029 142507274968011913115321)
                ·
                  rfl

theorem cell22_3746681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 7].length) (baseStart_3746681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3746681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3746681 prefixEnd_3746681 := by exact prefixLift 3746681
  have htrace : WordTrace (prefixWord ++ tailWord_3746681) baseStart_3746681 baseEnd_3746681 := by
    simpa [prefixWord, tailWord_3746681, baseEnd_3746681] using wordTrace_append hprefix tailTrace_3746681
  have hstable : (prefixWord ++ tailWord_3746681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746681).length < 2 ^ (prefixWord ++ tailWord_3746681).sum := by decide
  have hdescent : baseEnd_3746681 < baseStart_3746681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746685 : List Nat := [1, 4, 1, 1, 2, 1, 6, 1, 2, 3]
def baseStart_3746685 : Nat := 118140960795 + 3746685 * 2 ^ 59
def prefixEnd_3746685 : Nat := 4983230072969 + 3 ^ 40 * 3746685 * 2
def baseEnd_3746685 : Nat := 1282566843993852540937877

theorem tailTrace_3746685 : CollatzResearch.WordTrace tailWord_3746685 prefixEnd_3746685 1282566843993852540937877 := by
  unfold tailWord_3746685
  simp only [CollatzResearch.WordTrace]
  refine ⟨136652828431407602699433509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91101885620938401799622339 136652828431407602699433509)
  ·
    refine ⟨25622405330888925506143783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136652828431407602699433509 25622405330888925506143783)
    ·
      refine ⟨38433607996333388259215675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25622405330888925506143783 38433607996333388259215675)
      ·
        refine ⟨57650411994500082388823513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38433607996333388259215675 57650411994500082388823513)
        ·
          refine ⟨43237808995875061791617635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57650411994500082388823513 43237808995875061791617635)
          ·
            refine ⟨64856713493812592687426453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43237808995875061791617635 64856713493812592687426453)
            ·
              refine ⟨3040158445022465282223115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 64856713493812592687426453 3040158445022465282223115)
              ·
                refine ⟨4560237667533697923334673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3040158445022465282223115 4560237667533697923334673)
                ·
                  refine ⟨3420178250650273442501005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4560237667533697923334673 3420178250650273442501005)
                  ·
                    refine ⟨1282566843993852540937877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3420178250650273442501005 1282566843993852540937877)
                    ·
                      rfl

theorem cell22_3746685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 6, 1, 2, 3].length) (baseStart_3746685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3746685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3746685 prefixEnd_3746685 := by exact prefixLift 3746685
  have htrace : WordTrace (prefixWord ++ tailWord_3746685) baseStart_3746685 baseEnd_3746685 := by
    simpa [prefixWord, tailWord_3746685, baseEnd_3746685] using wordTrace_append hprefix tailTrace_3746685
  have hstable : (prefixWord ++ tailWord_3746685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746685).length < 2 ^ (prefixWord ++ tailWord_3746685).sum := by decide
  have hdescent : baseEnd_3746685 < baseStart_3746685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746925 : List Nat := [1, 5, 1, 1, 2, 2, 2, 1, 3, 4]
def baseStart_3746925 : Nat := 118140960795 + 3746925 * 2 ^ 59
def prefixEnd_3746925 : Nat := 4983230072969 + 3 ^ 40 * 3746925 * 2
def baseEnd_3746925 : Nat := 1282649000898571914937141

theorem tailTrace_3746925 : CollatzResearch.WordTrace tailWord_3746925 prefixEnd_3746925 1282649000898571914937141 := by
  unfold tailWord_3746925
  simp only [CollatzResearch.WordTrace]
  refine ⟨136661581950538123688170229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91107721300358749125446819 136661581950538123688170229)
  ·
    refine ⟨12812023307862949095765959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 136661581950538123688170229 12812023307862949095765959)
    ·
      refine ⟨19218034961794423643648939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12812023307862949095765959 19218034961794423643648939)
      ·
        refine ⟨28827052442691635465473409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19218034961794423643648939 28827052442691635465473409)
        ·
          refine ⟨21620289332018726599105057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28827052442691635465473409 21620289332018726599105057)
          ·
            refine ⟨16215216999014044949328793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21620289332018726599105057 16215216999014044949328793)
            ·
              refine ⟨12161412749260533711996595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16215216999014044949328793 12161412749260533711996595)
              ·
                refine ⟨18242119123890800567994893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12161412749260533711996595 18242119123890800567994893)
                ·
                  refine ⟨6840794671459050212998085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18242119123890800567994893 6840794671459050212998085)
                  ·
                    refine ⟨1282649000898571914937141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6840794671459050212998085 1282649000898571914937141)
                    ·
                      rfl

theorem cell22_3746925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_3746925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3746925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3746925 prefixEnd_3746925 := by exact prefixLift 3746925
  have htrace : WordTrace (prefixWord ++ tailWord_3746925) baseStart_3746925 baseEnd_3746925 := by
    simpa [prefixWord, tailWord_3746925, baseEnd_3746925] using wordTrace_append hprefix tailTrace_3746925
  have hstable : (prefixWord ++ tailWord_3746925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746925).length < 2 ^ (prefixWord ++ tailWord_3746925).sum := by decide
  have hdescent : baseEnd_3746925 < baseStart_3746925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746970 : List Nat := [3, 1, 1, 5, 1, 1, 1, 2, 1, 6]
def baseStart_3746970 : Nat := 118140960795 + 3746970 * 2 ^ 59
def prefixEnd_3746970 : Nat := 4983230072969 + 3 ^ 40 * 3746970 * 2
def baseEnd_3746970 : Nat := 1282664405318206797562003

theorem tailTrace_3746970 : CollatzResearch.WordTrace tailWord_3746970 prefixEnd_3746970 1282664405318206797562003 := by
  unfold tailWord_3746970
  simp only [CollatzResearch.WordTrace]
  refine ⟨34165805808843774093389591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91108815490250064249038909 34165805808843774093389591)
  ·
    refine ⟨51248708713265661140084387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34165805808843774093389591 51248708713265661140084387)
    ·
      refine ⟨76873063069898491710126581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51248708713265661140084387 76873063069898491710126581)
      ·
        refine ⟨7206849662802983597824367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76873063069898491710126581 7206849662802983597824367)
        ·
          refine ⟨10810274494204475396736551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7206849662802983597824367 10810274494204475396736551)
          ·
            refine ⟨16215411741306713095104827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10810274494204475396736551 16215411741306713095104827)
            ·
              refine ⟨24323117611960069642657241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16215411741306713095104827 24323117611960069642657241)
              ·
                refine ⟨18242338208970052231992931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24323117611960069642657241 18242338208970052231992931)
                ·
                  refine ⟨27363507313455078347989397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18242338208970052231992931 27363507313455078347989397)
                  ·
                    refine ⟨1282664405318206797562003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27363507313455078347989397 1282664405318206797562003)
                    ·
                      rfl

theorem cell22_3746970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 1, 6].length) (baseStart_3746970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3746970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3746970 prefixEnd_3746970 := by exact prefixLift 3746970
  have htrace : WordTrace (prefixWord ++ tailWord_3746970) baseStart_3746970 baseEnd_3746970 := by
    simpa [prefixWord, tailWord_3746970, baseEnd_3746970] using wordTrace_append hprefix tailTrace_3746970
  have hstable : (prefixWord ++ tailWord_3746970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746970).length < 2 ^ (prefixWord ++ tailWord_3746970).sum := by decide
  have hdescent : baseEnd_3746970 < baseStart_3746970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746972 : List Nat := [2, 2, 3, 2, 1, 4, 1, 1, 1, 5]
def baseStart_3746972 : Nat := 118140960795 + 3746972 * 2 ^ 59
def prefixEnd_3746972 : Nat := 4983230072969 + 3 ^ 40 * 3746972 * 2
def baseEnd_3746972 : Nat := 1282665089959079459011997

theorem tailTrace_3746972 : CollatzResearch.WordTrace tailWord_3746972 prefixEnd_3746972 1282665089959079459011997 := by
  unfold tailWord_3746972
  simp only [CollatzResearch.WordTrace]
  refine ⟨68331648090683925357565585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91108864120911900476754113 68331648090683925357565585)
  ·
    refine ⟨51248736068012944018174189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68331648090683925357565585 51248736068012944018174189)
    ·
      refine ⟨19218276025504854006815321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51248736068012944018174189 19218276025504854006815321)
      ·
        refine ⟨14413707019128640505111491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19218276025504854006815321 14413707019128640505111491)
        ·
          refine ⟨21620560528692960757667237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14413707019128640505111491 21620560528692960757667237)
          ·
            refine ⟨4053855099129930142062607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21620560528692960757667237 4053855099129930142062607)
            ·
              refine ⟨6080782648694895213093911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4053855099129930142062607 6080782648694895213093911)
              ·
                refine ⟨9121173973042342819640867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6080782648694895213093911 9121173973042342819640867)
                ·
                  refine ⟨13681760959563514229461301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9121173973042342819640867 13681760959563514229461301)
                  ·
                    refine ⟨1282665089959079459011997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13681760959563514229461301 1282665089959079459011997)
                    ·
                      rfl

theorem cell22_3746972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 1, 1, 5].length) (baseStart_3746972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3746972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3746972 prefixEnd_3746972 := by exact prefixLift 3746972
  have htrace : WordTrace (prefixWord ++ tailWord_3746972) baseStart_3746972 baseEnd_3746972 := by
    simpa [prefixWord, tailWord_3746972, baseEnd_3746972] using wordTrace_append hprefix tailTrace_3746972
  have hstable : (prefixWord ++ tailWord_3746972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746972).length < 2 ^ (prefixWord ++ tailWord_3746972).sum := by decide
  have hdescent : baseEnd_3746972 < baseStart_3746972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747068 : List Nat := [2, 2, 2, 1, 5, 2, 2, 2, 1, 3]
def baseStart_3747068 : Nat := 118140960795 + 3747068 * 2 ^ 59
def prefixEnd_3747068 : Nat := 4983230072969 + 3 ^ 40 * 3747068 * 2
def baseEnd_3747068 : Nat := 1282697952720967208611703

theorem tailTrace_3747068 : CollatzResearch.WordTrace tailWord_3747068 prefixEnd_3747068 1282697952720967208611703 := by
  unfold tailWord_3747068
  simp only [CollatzResearch.WordTrace]
  refine ⟨68333398794510029555312929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91111198392680039407083905 68333398794510029555312929)
  ·
    refine ⟨51250049095882522166484697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68333398794510029555312929 51250049095882522166484697)
    ·
      refine ⟨38437536821911891624863523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51250049095882522166484697 38437536821911891624863523)
      ·
        refine ⟨57656305232867837437295285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38437536821911891624863523 57656305232867837437295285)
        ·
          refine ⟨5405278615581359759746433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57656305232867837437295285 5405278615581359759746433)
          ·
            refine ⟨4053958961686019819809825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5405278615581359759746433 4053958961686019819809825)
            ·
              refine ⟨3040469221264514864857369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4053958961686019819809825 3040469221264514864857369)
              ·
                refine ⟨2280351915948386148643027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3040469221264514864857369 2280351915948386148643027)
                ·
                  refine ⟨3420527873922579222964541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2280351915948386148643027 3420527873922579222964541)
                  ·
                    refine ⟨1282697952720967208611703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3420527873922579222964541 1282697952720967208611703)
                    ·
                      rfl

theorem cell22_3747068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 2, 2, 1, 3].length) (baseStart_3747068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3747068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3747068 prefixEnd_3747068 := by exact prefixLift 3747068
  have htrace : WordTrace (prefixWord ++ tailWord_3747068) baseStart_3747068 baseEnd_3747068 := by
    simpa [prefixWord, tailWord_3747068, baseEnd_3747068] using wordTrace_append hprefix tailTrace_3747068
  have hstable : (prefixWord ++ tailWord_3747068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747068).length < 2 ^ (prefixWord ++ tailWord_3747068).sum := by decide
  have hdescent : baseEnd_3747068 < baseStart_3747068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747109 : List Nat := [1, 3, 1, 2, 4, 2, 2, 3, 4]
def baseStart_3747109 : Nat := 118140960795 + 3747109 * 2 ^ 59
def prefixEnd_3747109 : Nat := 4983230072969 + 3 ^ 40 * 3747109 * 2
def baseEnd_3747109 : Nat := 427570662619618922778859

theorem tailTrace_3747109 : CollatzResearch.WordTrace tailWord_3747109 prefixEnd_3747109 427570662619618922778859 := by
  unfold tailWord_3747109
  simp only [CollatzResearch.WordTrace]
  refine ⟨136668292981871523112868381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91112195321247682075245587 136668292981871523112868381)
  ·
    refine ⟨51250609868201821167325643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136668292981871523112868381 51250609868201821167325643)
    ·
      refine ⟨76875914802302731750988465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51250609868201821167325643 76875914802302731750988465)
      ·
        refine ⟨57656936101727048813241349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76875914802302731750988465 57656936101727048813241349)
        ·
          refine ⟨10810675519073821652482753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57656936101727048813241349 10810675519073821652482753)
          ·
            refine ⟨8108006639305366239362065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10810675519073821652482753 8108006639305366239362065)
            ·
              refine ⟨6081004979479024679521549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8108006639305366239362065 6081004979479024679521549)
              ·
                refine ⟨2280376867304634254820581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6081004979479024679521549 2280376867304634254820581)
                ·
                  refine ⟨427570662619618922778859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2280376867304634254820581 427570662619618922778859)
                  ·
                    rfl

theorem cell22_3747109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 3, 4].length) (baseStart_3747109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3747109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3747109 prefixEnd_3747109 := by exact prefixLift 3747109
  have htrace : WordTrace (prefixWord ++ tailWord_3747109) baseStart_3747109 baseEnd_3747109 := by
    simpa [prefixWord, tailWord_3747109, baseEnd_3747109] using wordTrace_append hprefix tailTrace_3747109
  have hstable : (prefixWord ++ tailWord_3747109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747109).length < 2 ^ (prefixWord ++ tailWord_3747109).sum := by decide
  have hdescent : baseEnd_3747109 < baseStart_3747109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747124 : List Nat := [2, 5, 1, 1, 1, 1, 3, 1, 4, 3]
def baseStart_3747124 : Nat := 118140960795 + 3747124 * 2 ^ 59
def prefixEnd_3747124 : Nat := 4983230072969 + 3 ^ 40 * 3747124 * 2
def baseEnd_3747124 : Nat := 1282717122665401729211531

theorem tailTrace_3747124 : CollatzResearch.WordTrace tailWord_3747124 prefixEnd_3747124 1282717122665401729211531 := by
  unfold tailWord_3747124
  simp only [CollatzResearch.WordTrace]
  refine ⟨68334420038408590337332213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91112560051211453783109617 68334420038408590337332213)
  ·
    refine ⟨6406351878600805344124895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68334420038408590337332213 6406351878600805344124895)
    ·
      refine ⟨9609527817901208016187343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6406351878600805344124895 9609527817901208016187343)
      ·
        refine ⟨14414291726851812024281015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9609527817901208016187343 14414291726851812024281015)
        ·
          refine ⟨21621437590277718036421523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14414291726851812024281015 21621437590277718036421523)
          ·
            refine ⟨32432156385416577054632285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21621437590277718036421523 32432156385416577054632285)
            ·
              refine ⟨12162058644531216395487107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32432156385416577054632285 12162058644531216395487107)
              ·
                refine ⟨18243087966796824593230661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12162058644531216395487107 18243087966796824593230661)
                ·
                  refine ⟨3420578993774404611230749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18243087966796824593230661 3420578993774404611230749)
                  ·
                    refine ⟨1282717122665401729211531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3420578993774404611230749 1282717122665401729211531)
                    ·
                      rfl

theorem cell22_3747124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_3747124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3747124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3747124 prefixEnd_3747124 := by exact prefixLift 3747124
  have htrace : WordTrace (prefixWord ++ tailWord_3747124) baseStart_3747124 baseEnd_3747124 := by
    simpa [prefixWord, tailWord_3747124, baseEnd_3747124] using wordTrace_append hprefix tailTrace_3747124
  have hstable : (prefixWord ++ tailWord_3747124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747124).length < 2 ^ (prefixWord ++ tailWord_3747124).sum := by decide
  have hdescent : baseEnd_3747124 < baseStart_3747124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747126 : List Nat := [5, 1, 2, 3, 1, 1, 2, 1, 6]
def baseStart_3747126 : Nat := 118140960795 + 3747126 * 2 ^ 59
def prefixEnd_3747126 : Nat := 4983230072969 + 3 ^ 40 * 3747126 * 2
def baseEnd_3747126 : Nat := 427572602435424796887175

theorem tailTrace_3747126 : CollatzResearch.WordTrace tailWord_3747126 prefixEnd_3747126 427572602435424796887175 := by
  unfold tailWord_3747126
  simp only [CollatzResearch.WordTrace]
  refine ⟨8541807063925620938514827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91112608681873290010824821 8541807063925620938514827)
  ·
    refine ⟨12812710595888431407772241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8541807063925620938514827 12812710595888431407772241)
    ·
      refine ⟨9609532946916323555829181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12812710595888431407772241 9609532946916323555829181)
      ·
        refine ⟨3603574855093621333435943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9609532946916323555829181 3603574855093621333435943)
        ·
          refine ⟨5405362282640432000153915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3603574855093621333435943 5405362282640432000153915)
          ·
            refine ⟨8108043423960648000230873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5405362282640432000153915 8108043423960648000230873)
            ·
              refine ⟨6081032567970486000173155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8108043423960648000230873 6081032567970486000173155)
              ·
                refine ⟨9121548851955729000259733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6081032567970486000173155 9121548851955729000259733)
                ·
                  refine ⟨427572602435424796887175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9121548851955729000259733 427572602435424796887175)
                  ·
                    rfl

theorem cell22_3747126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 1, 6].length) (baseStart_3747126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3747126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3747126 prefixEnd_3747126 := by exact prefixLift 3747126
  have htrace : WordTrace (prefixWord ++ tailWord_3747126) baseStart_3747126 baseEnd_3747126 := by
    simpa [prefixWord, tailWord_3747126, baseEnd_3747126] using wordTrace_append hprefix tailTrace_3747126
  have hstable : (prefixWord ++ tailWord_3747126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747126).length < 2 ^ (prefixWord ++ tailWord_3747126).sum := by decide
  have hdescent : baseEnd_3747126 < baseStart_3747126 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747152 : List Nat := [2, 1, 1, 1, 1, 5, 1, 4, 3, 3]
def baseStart_3747152 : Nat := 118140960795 + 3747152 * 2 ^ 59
def prefixEnd_3747152 : Nat := 4983230072969 + 3 ^ 40 * 3747152 * 2
def baseEnd_3747152 : Nat := 1282726707637618989511445

theorem tailTrace_3747152 : CollatzResearch.WordTrace tailWord_3747152 prefixEnd_3747152 1282726707637618989511445 := by
  unfold tailWord_3747152
  simp only [CollatzResearch.WordTrace]
  refine ⟨68334930660357870728341855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91113240880477160971122473 68334930660357870728341855)
  ·
    refine ⟨102502395990536806092512783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68334930660357870728341855 102502395990536806092512783)
    ·
      refine ⟨153753593985805209138769175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102502395990536806092512783 153753593985805209138769175)
      ·
        refine ⟨230630390978707813708153763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153753593985805209138769175 230630390978707813708153763)
        ·
          refine ⟨345945586468061720562230645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230630390978707813708153763 345945586468061720562230645)
          ·
            refine ⟨32432398731380786302709123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 345945586468061720562230645 32432398731380786302709123)
            ·
              refine ⟨48648598097071179454063685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32432398731380786302709123 48648598097071179454063685)
              ·
                refine ⟨9121612143200846147636941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48648598097071179454063685 9121612143200846147636941)
                ·
                  refine ⟨3420604553700317305363853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9121612143200846147636941 3420604553700317305363853)
                  ·
                    refine ⟨1282726707637618989511445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3420604553700317305363853 1282726707637618989511445)
                    ·
                      rfl

theorem cell22_3747152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 4, 3, 3].length) (baseStart_3747152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3747152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3747152 prefixEnd_3747152 := by exact prefixLift 3747152
  have htrace : WordTrace (prefixWord ++ tailWord_3747152) baseStart_3747152 baseEnd_3747152 := by
    simpa [prefixWord, tailWord_3747152, baseEnd_3747152] using wordTrace_append hprefix tailTrace_3747152
  have hstable : (prefixWord ++ tailWord_3747152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747152).length < 2 ^ (prefixWord ++ tailWord_3747152).sum := by decide
  have hdescent : baseEnd_3747152 < baseStart_3747152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747212 : List Nat := [2, 2, 1, 2, 1, 3, 3, 1, 3, 4]
def baseStart_3747212 : Nat := 118140960795 + 3747212 * 2 ^ 59
def prefixEnd_3747212 : Nat := 4983230072969 + 3 ^ 40 * 3747212 * 2
def baseEnd_3747212 : Nat := 1282747246863798833011261

theorem tailTrace_3747212 : CollatzResearch.WordTrace tailWord_3747212 prefixEnd_3747212 1282747246863798833011261 := by
  unfold tailWord_3747212
  simp only [CollatzResearch.WordTrace]
  refine ⟨68336024850249185851933945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91114699800332247802578593 68336024850249185851933945)
  ·
    refine ⟨51252018637686889388950459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68336024850249185851933945 51252018637686889388950459)
    ·
      refine ⟨76878027956530334083425689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51252018637686889388950459 76878027956530334083425689)
      ·
        refine ⟨57658520967397750562569267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76878027956530334083425689 57658520967397750562569267)
        ·
          refine ⟨86487781451096625843853901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57658520967397750562569267 86487781451096625843853901)
          ·
            refine ⟨32432918044161234691445213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86487781451096625843853901 32432918044161234691445213)
            ·
              refine ⟨12162344266560463009291955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32432918044161234691445213 12162344266560463009291955)
              ·
                refine ⟨18243516399840694513937933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12162344266560463009291955 18243516399840694513937933)
                ·
                  refine ⟨6841318649940260442726725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18243516399840694513937933 6841318649940260442726725)
                  ·
                    refine ⟨1282747246863798833011261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6841318649940260442726725 1282747246863798833011261)
                    ·
                      rfl

theorem cell22_3747212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 3, 4].length) (baseStart_3747212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3747212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3747212 prefixEnd_3747212 := by exact prefixLift 3747212
  have htrace : WordTrace (prefixWord ++ tailWord_3747212) baseStart_3747212 baseEnd_3747212 := by
    simpa [prefixWord, tailWord_3747212, baseEnd_3747212] using wordTrace_append hprefix tailTrace_3747212
  have hstable : (prefixWord ++ tailWord_3747212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747212).length < 2 ^ (prefixWord ++ tailWord_3747212).sum := by decide
  have hdescent : baseEnd_3747212 < baseStart_3747212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747274 : List Nat := [3, 1, 2, 1, 2, 3, 3, 1, 2, 4]
def baseStart_3747274 : Nat := 118140960795 + 3747274 * 2 ^ 59
def prefixEnd_3747274 : Nat := 4983230072969 + 3 ^ 40 * 3747274 * 2
def baseEnd_3747274 : Nat := 1282768470730851337961071

theorem tailTrace_3747274 : CollatzResearch.WordTrace tailWord_3747274 prefixEnd_3747274 1282768470730851337961071 := by
  unfold tailWord_3747274
  simp only [CollatzResearch.WordTrace]
  refine ⟨34168577756568439073156219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91116207350849170861749917 34168577756568439073156219)
  ·
    refine ⟨51252866634852658609734329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34168577756568439073156219 51252866634852658609734329)
    ·
      refine ⟨38439649976139493957300747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51252866634852658609734329 38439649976139493957300747)
      ·
        refine ⟨57659474964209240935951121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38439649976139493957300747 57659474964209240935951121)
        ·
          refine ⟨43244606223156930701963341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57659474964209240935951121 43244606223156930701963341)
          ·
            refine ⟨16216727333683849013236253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43244606223156930701963341 16216727333683849013236253)
            ·
              refine ⟨6081272750131443379963595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16216727333683849013236253 6081272750131443379963595)
              ·
                refine ⟨9121909125197165069945393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6081272750131443379963595 9121909125197165069945393)
                ·
                  refine ⟨6841431843897873802459045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9121909125197165069945393 6841431843897873802459045)
                  ·
                    refine ⟨1282768470730851337961071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6841431843897873802459045 1282768470730851337961071)
                    ·
                      rfl

theorem cell22_3747274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 1, 2, 4].length) (baseStart_3747274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3747274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3747274 prefixEnd_3747274 := by exact prefixLift 3747274
  have htrace : WordTrace (prefixWord ++ tailWord_3747274) baseStart_3747274 baseEnd_3747274 := by
    simpa [prefixWord, tailWord_3747274, baseEnd_3747274] using wordTrace_append hprefix tailTrace_3747274
  have hstable : (prefixWord ++ tailWord_3747274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747274).length < 2 ^ (prefixWord ++ tailWord_3747274).sum := by decide
  have hdescent : baseEnd_3747274 < baseStart_3747274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747293 : List Nat := [1, 4, 3, 1, 1, 4, 1, 2, 2, 3]
def baseStart_3747293 : Nat := 118140960795 + 3747293 * 2 ^ 59
def prefixEnd_3747293 : Nat := 4983230072969 + 3 ^ 40 * 3747293 * 2
def baseEnd_3747293 : Nat := 1282774974819141621736013

theorem tailTrace_3747293 : CollatzResearch.WordTrace tailWord_3747293 prefixEnd_3747293 1282774974819141621736013 := by
  unfold tailWord_3747293
  simp only [CollatzResearch.WordTrace]
  refine ⟨136675004013204922537566533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91116669342136615025044355 136675004013204922537566533)
  ·
    refine ⟨25626563252475922975793725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136675004013204922537566533 25626563252475922975793725)
    ·
      refine ⟨9609961219678471115922647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25626563252475922975793725 9609961219678471115922647)
      ·
        refine ⟨14414941829517706673883971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9609961219678471115922647 14414941829517706673883971)
        ·
          refine ⟨21622412744276560010825957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14414941829517706673883971 21622412744276560010825957)
          ·
            refine ⟨4054202389551855002029867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21622412744276560010825957 4054202389551855002029867)
            ·
              refine ⟨6081303584327782503044801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4054202389551855002029867 6081303584327782503044801)
              ·
                refine ⟨4560977688245836877283601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6081303584327782503044801 4560977688245836877283601)
                ·
                  refine ⟨3420733266184377657962701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4560977688245836877283601 3420733266184377657962701)
                  ·
                    refine ⟨1282774974819141621736013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3420733266184377657962701 1282774974819141621736013)
                    ·
                      rfl

theorem cell22_3747293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_3747293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3747293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3747293 prefixEnd_3747293 := by exact prefixLift 3747293
  have htrace : WordTrace (prefixWord ++ tailWord_3747293) baseStart_3747293 baseEnd_3747293 := by
    simpa [prefixWord, tailWord_3747293, baseEnd_3747293] using wordTrace_append hprefix tailTrace_3747293
  have hstable : (prefixWord ++ tailWord_3747293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747293).length < 2 ^ (prefixWord ++ tailWord_3747293).sum := by decide
  have hdescent : baseEnd_3747293 < baseStart_3747293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747338 : List Nat := [3, 1, 2, 2, 2, 2, 3, 3, 1, 3]
def baseStart_3747338 : Nat := 118140960795 + 3747338 * 2 ^ 59
def prefixEnd_3747338 : Nat := 4983230072969 + 3 ^ 40 * 3747338 * 2
def baseEnd_3747338 : Nat := 1282790379238776504360875

theorem tailTrace_3747338 : CollatzResearch.WordTrace tailWord_3747338 prefixEnd_3747338 1282790379238776504360875 := by
  unfold tailWord_3747338
  simp only [CollatzResearch.WordTrace]
  refine ⟨34169161324510473805738667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91117763532027930148636445 34169161324510473805738667)
  ·
    refine ⟨51253741986765710708608001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34169161324510473805738667 51253741986765710708608001)
    ·
      refine ⟨38440306490074283031456001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51253741986765710708608001 38440306490074283031456001)
      ·
        refine ⟨28830229867555712273592001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38440306490074283031456001 28830229867555712273592001)
        ·
          refine ⟨21622672400666784205194001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28830229867555712273592001 21622672400666784205194001)
          ·
            refine ⟨16217004300500088153895501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21622672400666784205194001 16217004300500088153895501)
            ·
              refine ⟨6081376612687533057710813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16217004300500088153895501 6081376612687533057710813)
              ·
                refine ⟨2280516229757824896641555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6081376612687533057710813 2280516229757824896641555)
                ·
                  refine ⟨3420774344636737344962333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2280516229757824896641555 3420774344636737344962333)
                  ·
                    refine ⟨1282790379238776504360875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3420774344636737344962333 1282790379238776504360875)
                    ·
                      rfl

theorem cell22_3747338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 3, 1, 3].length) (baseStart_3747338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3747338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3747338 prefixEnd_3747338 := by exact prefixLift 3747338
  have htrace : WordTrace (prefixWord ++ tailWord_3747338) baseStart_3747338 baseEnd_3747338 := by
    simpa [prefixWord, tailWord_3747338, baseEnd_3747338] using wordTrace_append hprefix tailTrace_3747338
  have hstable : (prefixWord ++ tailWord_3747338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747338).length < 2 ^ (prefixWord ++ tailWord_3747338).sum := by decide
  have hdescent : baseEnd_3747338 < baseStart_3747338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747381 : List Nat := [1, 3, 3, 1, 1, 3, 3, 2, 1, 4]
def baseStart_3747381 : Nat := 118140960795 + 3747381 * 2 ^ 59
def prefixEnd_3747381 : Nat := 4983230072969 + 3 ^ 40 * 3747381 * 2
def baseEnd_3747381 : Nat := 1282805099017538725535743

theorem tailTrace_3747381 : CollatzResearch.WordTrace tailWord_3747381 prefixEnd_3747381 1282805099017538725535743 := by
  unfold tailWord_3747381
  simp only [CollatzResearch.WordTrace]
  refine ⟨136678213636886113566769997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91118809091257409044513331 136678213636886113566769997)
  ·
    refine ⟨51254330113832292587538749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136678213636886113566769997 51254330113832292587538749)
    ·
      refine ⟨19220373792687109720327031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51254330113832292587538749 19220373792687109720327031)
      ·
        refine ⟨28830560689030664580490547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19220373792687109720327031 28830560689030664580490547)
        ·
          refine ⟨43245841033545996870735821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28830560689030664580490547 43245841033545996870735821)
          ·
            refine ⟨16217190387579748826525933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43245841033545996870735821 16217190387579748826525933)
            ·
              refine ⟨6081446395342405809947225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16217190387579748826525933 6081446395342405809947225)
              ·
                refine ⟨4561084796506804357460419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6081446395342405809947225 4561084796506804357460419)
                ·
                  refine ⟨6841627194760206536190629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4561084796506804357460419 6841627194760206536190629)
                  ·
                    refine ⟨1282805099017538725535743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6841627194760206536190629 1282805099017538725535743)
                    ·
                      rfl

theorem cell22_3747381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_3747381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3747381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3747381 prefixEnd_3747381 := by exact prefixLift 3747381
  have htrace : WordTrace (prefixWord ++ tailWord_3747381) baseStart_3747381 baseEnd_3747381 := by
    simpa [prefixWord, tailWord_3747381, baseEnd_3747381] using wordTrace_append hprefix tailTrace_3747381
  have hstable : (prefixWord ++ tailWord_3747381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747381).length < 2 ^ (prefixWord ++ tailWord_3747381).sum := by decide
  have hdescent : baseEnd_3747381 < baseStart_3747381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747409 : List Nat := [1, 2, 2, 1, 3, 2, 1, 4, 2, 4]
def baseStart_3747409 : Nat := 118140960795 + 3747409 * 2 ^ 59
def prefixEnd_3747409 : Nat := 4983230072969 + 3 ^ 40 * 3747409 * 2
def baseEnd_3747409 : Nat := 1282814683989755985835657

theorem tailTrace_3747409 : CollatzResearch.WordTrace tailWord_3747409 prefixEnd_3747409 1282814683989755985835657 := by
  unfold tailWord_3747409
  simp only [CollatzResearch.WordTrace]
  refine ⟨136679234880784674348789281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91119489920523116232526187 136679234880784674348789281)
  ·
    refine ⟨102509426160588505761591961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136679234880784674348789281 102509426160588505761591961)
    ·
      refine ⟨76882069620441379321193971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102509426160588505761591961 76882069620441379321193971)
      ·
        refine ⟨115323104430662068981790957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76882069620441379321193971 115323104430662068981790957)
        ·
          refine ⟨43246164161498275868171609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115323104430662068981790957 43246164161498275868171609)
          ·
            refine ⟨32434623121123706901128707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43246164161498275868171609 32434623121123706901128707)
            ·
              refine ⟨48651934681685560351693061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32434623121123706901128707 48651934681685560351693061)
              ·
                refine ⟨9122237752816042565942449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48651934681685560351693061 9122237752816042565942449)
                ·
                  refine ⟨6841678314612031924456837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9122237752816042565942449 6841678314612031924456837)
                  ·
                    refine ⟨1282814683989755985835657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6841678314612031924456837 1282814683989755985835657)
                    ·
                      rfl

theorem cell22_3747409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 4, 2, 4].length) (baseStart_3747409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3747409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3747409 prefixEnd_3747409 := by exact prefixLift 3747409
  have htrace : WordTrace (prefixWord ++ tailWord_3747409) baseStart_3747409 baseEnd_3747409 := by
    simpa [prefixWord, tailWord_3747409, baseEnd_3747409] using wordTrace_append hprefix tailTrace_3747409
  have hstable : (prefixWord ++ tailWord_3747409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747409).length < 2 ^ (prefixWord ++ tailWord_3747409).sum := by decide
  have hdescent : baseEnd_3747409 < baseStart_3747409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747531 : List Nat := [1, 1, 1, 1, 3, 2, 1, 8, 4]
def baseStart_3747531 : Nat := 118140960795 + 3747531 * 2 ^ 59
def prefixEnd_3747531 : Nat := 4983230072969 + 3 ^ 40 * 3747531 * 2
def baseEnd_3747531 : Nat := 427618815694329444761761

theorem tailTrace_3747531 : CollatzResearch.WordTrace tailWord_3747531 prefixEnd_3747531 427618815694329444761761 := by
  unfold tailWord_3747531
  simp only [CollatzResearch.WordTrace]
  refine ⟨136683684586342689184730447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91122456390895126123153631 136683684586342689184730447)
  ·
    refine ⟨205025526879514033777095671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136683684586342689184730447 205025526879514033777095671)
    ·
      refine ⟨307538290319271050665643507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205025526879514033777095671 307538290319271050665643507)
      ·
        refine ⟨461307435478906575998465261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307538290319271050665643507 461307435478906575998465261)
        ·
          refine ⟨172990288304589965999424473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 461307435478906575998465261 172990288304589965999424473)
          ·
            refine ⟨129742716228442474499568355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172990288304589965999424473 129742716228442474499568355)
            ·
              refine ⟨194614074342663711749352533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129742716228442474499568355 194614074342663711749352533)
              ·
                refine ⟨2280633683703090372062725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 194614074342663711749352533 2280633683703090372062725)
                ·
                  refine ⟨427618815694329444761761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2280633683703090372062725 427618815694329444761761)
                  ·
                    rfl

theorem cell22_3747531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 8, 4].length) (baseStart_3747531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3747531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3747531 prefixEnd_3747531 := by exact prefixLift 3747531
  have htrace : WordTrace (prefixWord ++ tailWord_3747531) baseStart_3747531 baseEnd_3747531 := by
    simpa [prefixWord, tailWord_3747531, baseEnd_3747531] using wordTrace_append hprefix tailTrace_3747531
  have hstable : (prefixWord ++ tailWord_3747531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747531).length < 2 ^ (prefixWord ++ tailWord_3747531).sum := by decide
  have hdescent : baseEnd_3747531 < baseStart_3747531 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747676 : List Nat := [2, 2, 4, 2, 3, 1, 1, 3, 1, 3]
def baseStart_3747676 : Nat := 118140960795 + 3747676 * 2 ^ 59
def prefixEnd_3747676 : Nat := 4983230072969 + 3 ^ 40 * 3747676 * 2
def baseEnd_3747676 : Nat := 1282906083546256289409839

theorem tailTrace_3747676 : CollatzResearch.WordTrace tailWord_3747676 prefixEnd_3747676 1282906083546256289409839 := by
  unfold tailWord_3747676
  simp only [CollatzResearch.WordTrace]
  refine ⟨68344486585408689474379441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91125982113878252632505921 68344486585408689474379441)
  ·
    refine ⟨51258364939056517105784581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68344486585408689474379441 51258364939056517105784581)
    ·
      refine ⟨9610943426073096957334609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51258364939056517105784581 9610943426073096957334609)
      ·
        refine ⟨7208207569554822718000957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9610943426073096957334609 7208207569554822718000957)
        ·
          refine ⟨2703077838583058519250359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7208207569554822718000957 2703077838583058519250359)
          ·
            refine ⟨4054616757874587778875539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2703077838583058519250359 4054616757874587778875539)
            ·
              refine ⟨6081925136811881668313309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4054616757874587778875539 6081925136811881668313309)
              ·
                refine ⟨2280721926304455625617491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6081925136811881668313309 2280721926304455625617491)
                ·
                  refine ⟨3421082889456683438426237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2280721926304455625617491 3421082889456683438426237)
                  ·
                    refine ⟨1282906083546256289409839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3421082889456683438426237 1282906083546256289409839)
                    ·
                      rfl

theorem cell22_3747676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_3747676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3747676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3747676 prefixEnd_3747676 := by exact prefixLift 3747676
  have htrace : WordTrace (prefixWord ++ tailWord_3747676) baseStart_3747676 baseEnd_3747676 := by
    simpa [prefixWord, tailWord_3747676, baseEnd_3747676] using wordTrace_append hprefix tailTrace_3747676
  have hstable : (prefixWord ++ tailWord_3747676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747676).length < 2 ^ (prefixWord ++ tailWord_3747676).sum := by decide
  have hdescent : baseEnd_3747676 < baseStart_3747676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747681 : List Nat := [1, 2, 3, 1, 1, 1, 4, 1, 3, 5]
def baseStart_3747681 : Nat := 118140960795 + 3747681 * 2 ^ 59
def prefixEnd_3747681 : Nat := 4983230072969 + 3 ^ 40 * 3747681 * 2
def baseEnd_3747681 : Nat := 1282907795148437943034823

theorem tailTrace_3747681 : CollatzResearch.WordTrace tailWord_3747681 prefixEnd_3747681 1282907795148437943034823 := by
  unfold tailWord_3747681
  simp only [CollatzResearch.WordTrace]
  refine ⟨136689155535799264802690897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91126103690532843201793931 136689155535799264802690897)
  ·
    refine ⟨102516866651849448602018173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136689155535799264802690897 102516866651849448602018173)
    ·
      refine ⟨38443824994443543225756815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102516866651849448602018173 38443824994443543225756815)
      ·
        refine ⟨57665737491665314838635223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38443824994443543225756815 57665737491665314838635223)
        ·
          refine ⟨86498606237497972257952835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57665737491665314838635223 86498606237497972257952835)
          ·
            refine ⟨129747909356246958386929253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86498606237497972257952835 129747909356246958386929253)
            ·
              refine ⟨24327733004296304697549235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129747909356246958386929253 24327733004296304697549235)
              ·
                refine ⟨36491599506444457046323853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24327733004296304697549235 36491599506444457046323853)
                ·
                  refine ⟨13684349814916671392371445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36491599506444457046323853 13684349814916671392371445)
                  ·
                    refine ⟨1282907795148437943034823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13684349814916671392371445 1282907795148437943034823)
                    ·
                      rfl

theorem cell22_3747681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_3747681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3747681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3747681 prefixEnd_3747681 := by exact prefixLift 3747681
  have htrace : WordTrace (prefixWord ++ tailWord_3747681) baseStart_3747681 baseEnd_3747681 := by
    simpa [prefixWord, tailWord_3747681, baseEnd_3747681] using wordTrace_append hprefix tailTrace_3747681
  have hstable : (prefixWord ++ tailWord_3747681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747681).length < 2 ^ (prefixWord ++ tailWord_3747681).sum := by decide
  have hdescent : baseEnd_3747681 < baseStart_3747681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747715 : List Nat := [1, 1, 1, 3, 4, 3, 1, 3, 2, 3]
def baseStart_3747715 : Nat := 118140960795 + 3747715 * 2 ^ 59
def prefixEnd_3747715 : Nat := 4983230072969 + 3 ^ 40 * 3747715 * 2
def baseEnd_3747715 : Nat := 1282919434043273187684719

theorem tailTrace_3747715 : CollatzResearch.WordTrace tailWord_3747715 prefixEnd_3747715 1282919434043273187684719 := by
  unfold tailWord_3747715
  simp only [CollatzResearch.WordTrace]
  refine ⟨136690395617676088609428599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91126930411784059072952399 136690395617676088609428599)
  ·
    refine ⟨205035593426514132914142899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136690395617676088609428599 205035593426514132914142899)
    ·
      refine ⟨307553390139771199371214349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205035593426514132914142899 307553390139771199371214349)
      ·
        refine ⟨115332521302414199764205381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 307553390139771199371214349 115332521302414199764205381)
        ·
          refine ⟨21624847744202662455788509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115332521302414199764205381 21624847744202662455788509)
          ·
            refine ⟨8109317904075998420920691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21624847744202662455788509 8109317904075998420920691)
            ·
              refine ⟨12163976856113997631381037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8109317904075998420920691 12163976856113997631381037)
              ·
                refine ⟨4561491321042749111767889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12163976856113997631381037 4561491321042749111767889)
                ·
                  refine ⟨3421118490782061833825917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4561491321042749111767889 3421118490782061833825917)
                  ·
                    refine ⟨1282919434043273187684719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3421118490782061833825917 1282919434043273187684719)
                    ·
                      rfl

theorem cell22_3747715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 3, 2, 3].length) (baseStart_3747715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3747715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3747715 prefixEnd_3747715 := by exact prefixLift 3747715
  have htrace : WordTrace (prefixWord ++ tailWord_3747715) baseStart_3747715 baseEnd_3747715 := by
    simpa [prefixWord, tailWord_3747715, baseEnd_3747715] using wordTrace_append hprefix tailTrace_3747715
  have hstable : (prefixWord ++ tailWord_3747715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747715).length < 2 ^ (prefixWord ++ tailWord_3747715).sum := by decide
  have hdescent : baseEnd_3747715 < baseStart_3747715 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747730 : List Nat := [3, 2, 3, 2, 1, 1, 1, 3, 2, 4]
def baseStart_3747730 : Nat := 118140960795 + 3747730 * 2 ^ 59
def prefixEnd_3747730 : Nat := 4983230072969 + 3 ^ 40 * 3747730 * 2
def baseEnd_3747730 : Nat := 1282924568849818148559673

theorem tailTrace_3747730 : CollatzResearch.WordTrace tailWord_3747730 prefixEnd_3747730 1282924568849818148559673 := by
  unfold tailWord_3747730
  simp only [CollatzResearch.WordTrace]
  refine ⟨34172735678155436542806161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91127295141747830780816429 34172735678155436542806161)
  ·
    refine ⟨25629551758616577407104621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34172735678155436542806161 25629551758616577407104621)
    ·
      refine ⟨9611081909481216527664233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25629551758616577407104621 9611081909481216527664233)
      ·
        refine ⟨7208311432110912395748175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9611081909481216527664233 7208311432110912395748175)
        ·
          refine ⟨10812467148166368593622263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7208311432110912395748175 10812467148166368593622263)
          ·
            refine ⟨16218700722249552890433395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10812467148166368593622263 16218700722249552890433395)
            ·
              refine ⟨24328051083374329335650093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16218700722249552890433395 24328051083374329335650093)
              ·
                refine ⟨9123019156265373500868785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24328051083374329335650093 9123019156265373500868785)
                ·
                  refine ⟨6842264367199030125651589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9123019156265373500868785 6842264367199030125651589)
                  ·
                    refine ⟨1282924568849818148559673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6842264367199030125651589 1282924568849818148559673)
                    ·
                      rfl

theorem cell22_3747730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_3747730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3747730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3747730 prefixEnd_3747730 := by exact prefixLift 3747730
  have htrace : WordTrace (prefixWord ++ tailWord_3747730) baseStart_3747730 baseEnd_3747730 := by
    simpa [prefixWord, tailWord_3747730, baseEnd_3747730] using wordTrace_append hprefix tailTrace_3747730
  have hstable : (prefixWord ++ tailWord_3747730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747730).length < 2 ^ (prefixWord ++ tailWord_3747730).sum := by decide
  have hdescent : baseEnd_3747730 < baseStart_3747730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747771 : List Nat := [1, 1, 1, 1, 1, 2, 2, 5, 1, 7]
def baseStart_3747771 : Nat := 118140960795 + 3747771 * 2 ^ 59
def prefixEnd_3747771 : Nat := 4983230072969 + 3 ^ 40 * 3747771 * 2
def baseEnd_3747771 : Nat := 1282938603987707708284547

theorem tailTrace_3747771 : CollatzResearch.WordTrace tailWord_3747771 prefixEnd_3747771 1282938603987707708284547 := by
  unfold tailWord_3747771
  simp only [CollatzResearch.WordTrace]
  refine ⟨136692438105473210173467167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91128292070315473448978111 136692438105473210173467167)
  ·
    refine ⟨205038657158209815260200751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136692438105473210173467167 205038657158209815260200751)
    ·
      refine ⟨307557985737314722890301127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205038657158209815260200751 307557985737314722890301127)
      ·
        refine ⟨461336978605972084335451691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307557985737314722890301127 461336978605972084335451691)
        ·
          refine ⟨692005467908958126503177537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 461336978605972084335451691 692005467908958126503177537)
          ·
            refine ⟨519004100931718594877383153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 692005467908958126503177537 519004100931718594877383153)
            ·
              refine ⟨389253075698788946158037365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 519004100931718594877383153 389253075698788946158037365)
              ·
                refine ⟨36492475846761463702316003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 389253075698788946158037365 36492475846761463702316003)
                ·
                  refine ⟨54738713770142195553474005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36492475846761463702316003 54738713770142195553474005)
                  ·
                    refine ⟨1282938603987707708284547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54738713770142195553474005 1282938603987707708284547)
                    ·
                      rfl

theorem cell22_3747771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 7].length) (baseStart_3747771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3747771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3747771 prefixEnd_3747771 := by exact prefixLift 3747771
  have htrace : WordTrace (prefixWord ++ tailWord_3747771) baseStart_3747771 baseEnd_3747771 := by
    simpa [prefixWord, tailWord_3747771, baseEnd_3747771] using wordTrace_append hprefix tailTrace_3747771
  have hstable : (prefixWord ++ tailWord_3747771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747771).length < 2 ^ (prefixWord ++ tailWord_3747771).sum := by decide
  have hdescent : baseEnd_3747771 < baseStart_3747771 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747848 : List Nat := [2, 1, 3, 2, 1, 2, 1, 3, 1, 6]
def baseStart_3747848 : Nat := 118140960795 + 3747848 * 2 ^ 59
def prefixEnd_3747848 : Nat := 4983230072969 + 3 ^ 40 * 3747848 * 2
def baseEnd_3747848 : Nat := 1282964962661305174109311

theorem tailTrace_3747848 : CollatzResearch.WordTrace tailWord_3747848 prefixEnd_3747848 1282964962661305174109311 := by
  unfold tailWord_3747848
  simp only [CollatzResearch.WordTrace]
  refine ⟨68347623263097126162010099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91130164350796168216013465 68347623263097126162010099)
  ·
    refine ⟨102521434894645689243015149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68347623263097126162010099 102521434894645689243015149)
    ·
      refine ⟨38445538085492133466130681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102521434894645689243015149 38445538085492133466130681)
      ·
        refine ⟨28834153564119100099598011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38445538085492133466130681 28834153564119100099598011)
        ·
          refine ⟨43251230346178650149397017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28834153564119100099598011 43251230346178650149397017)
          ·
            refine ⟨32438422759633987612047763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43251230346178650149397017 32438422759633987612047763)
            ·
              refine ⟨48657634139450981418071645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32438422759633987612047763 48657634139450981418071645)
              ·
                refine ⟨18246612802294118031776867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48657634139450981418071645 18246612802294118031776867)
                ·
                  refine ⟨27369919203441177047665301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18246612802294118031776867 27369919203441177047665301)
                  ·
                    refine ⟨1282964962661305174109311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27369919203441177047665301 1282964962661305174109311)
                    ·
                      rfl

theorem cell22_3747848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_3747848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3747848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3747848 prefixEnd_3747848 := by exact prefixLift 3747848
  have htrace : WordTrace (prefixWord ++ tailWord_3747848) baseStart_3747848 baseEnd_3747848 := by
    simpa [prefixWord, tailWord_3747848, baseEnd_3747848] using wordTrace_append hprefix tailTrace_3747848
  have hstable : (prefixWord ++ tailWord_3747848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747848).length < 2 ^ (prefixWord ++ tailWord_3747848).sum := by decide
  have hdescent : baseEnd_3747848 < baseStart_3747848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747869 : List Nat := [1, 4, 2, 2, 2, 2, 3, 2, 4]
def baseStart_3747869 : Nat := 118140960795 + 3747869 * 2 ^ 59
def prefixEnd_3747869 : Nat := 4983230072969 + 3 ^ 40 * 3747869 * 2
def baseEnd_3747869 : Nat := 427657383796822706444749

theorem tailTrace_3747869 : CollatzResearch.WordTrace tailWord_3747869 prefixEnd_3747869 427657383796822706444749 := by
  unfold tailWord_3747869
  simp only [CollatzResearch.WordTrace]
  refine ⟨136696012459118172910534661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91130674972745448607023107 136696012459118172910534661)
  ·
    refine ⟨25630502336084657420725249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136696012459118172910534661 25630502336084657420725249)
    ·
      refine ⟨19222876752063493065543937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25630502336084657420725249 19222876752063493065543937)
      ·
        refine ⟨14417157564047619799157953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19222876752063493065543937 14417157564047619799157953)
        ·
          refine ⟨10812868173035714849368465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14417157564047619799157953 10812868173035714849368465)
          ·
            refine ⟨8109651129776786137026349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10812868173035714849368465 8109651129776786137026349)
            ·
              refine ⟨3041119173666294801384881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8109651129776786137026349 3041119173666294801384881)
              ·
                refine ⟨2280839380249721101038661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3041119173666294801384881 2280839380249721101038661)
                ·
                  refine ⟨427657383796822706444749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2280839380249721101038661 427657383796822706444749)
                  ·
                    rfl

theorem cell22_3747869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 3, 2, 4].length) (baseStart_3747869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3747869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3747869 prefixEnd_3747869 := by exact prefixLift 3747869
  have htrace : WordTrace (prefixWord ++ tailWord_3747869) baseStart_3747869 baseEnd_3747869 := by
    simpa [prefixWord, tailWord_3747869, baseEnd_3747869] using wordTrace_append hprefix tailTrace_3747869
  have hstable : (prefixWord ++ tailWord_3747869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747869).length < 2 ^ (prefixWord ++ tailWord_3747869).sum := by decide
  have hdescent : baseEnd_3747869 < baseStart_3747869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747895 : List Nat := [1, 1, 3, 1, 2, 2, 2, 4, 3, 3]
def baseStart_3747895 : Nat := 118140960795 + 3747895 * 2 ^ 59
def prefixEnd_3747895 : Nat := 4983230072969 + 3 ^ 40 * 3747895 * 2
def baseEnd_3747895 : Nat := 1282981051721812718184167

theorem tailTrace_3747895 : CollatzResearch.WordTrace tailWord_3747895 prefixEnd_3747895 1282981051721812718184167 := by
  unfold tailWord_3747895
  simp only [CollatzResearch.WordTrace]
  refine ⟨136696960757023979350981139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91131307171349319567320759 136696960757023979350981139)
  ·
    refine ⟨205045441135535969026471709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136696960757023979350981139 205045441135535969026471709)
    ·
      refine ⟨76892040425825988384926891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205045441135535969026471709 76892040425825988384926891)
      ·
        refine ⟨115338060638738982577390337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76892040425825988384926891 115338060638738982577390337)
        ·
          refine ⟨86503545479054236933042753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115338060638738982577390337 86503545479054236933042753)
          ·
            refine ⟨64877659109290677699782065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86503545479054236933042753 64877659109290677699782065)
            ·
              refine ⟨48658244331968008274836549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64877659109290677699782065 48658244331968008274836549)
              ·
                refine ⟨9123420812244001551531853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48658244331968008274836549 9123420812244001551531853)
                ·
                  refine ⟨3421282804591500581824445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9123420812244001551531853 3421282804591500581824445)
                  ·
                    refine ⟨1282981051721812718184167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3421282804591500581824445 1282981051721812718184167)
                    ·
                      rfl

theorem cell22_3747895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 4, 3, 3].length) (baseStart_3747895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3747895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3747895 prefixEnd_3747895 := by exact prefixLift 3747895
  have htrace : WordTrace (prefixWord ++ tailWord_3747895) baseStart_3747895 baseEnd_3747895 := by
    simpa [prefixWord, tailWord_3747895, baseEnd_3747895] using wordTrace_append hprefix tailTrace_3747895
  have hstable : (prefixWord ++ tailWord_3747895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747895).length < 2 ^ (prefixWord ++ tailWord_3747895).sum := by decide
  have hdescent : baseEnd_3747895 < baseStart_3747895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747925 : List Nat := [1, 3, 2, 2, 1, 3, 1, 4, 5]
def baseStart_3747925 : Nat := 118140960795 + 3747925 * 2 ^ 59
def prefixEnd_3747925 : Nat := 4983230072969 + 3 ^ 40 * 3747925 * 2
def baseEnd_3747925 : Nat := 427663773778300879978025

theorem tailTrace_3747925 : CollatzResearch.WordTrace tailWord_3747925 prefixEnd_3747925 427663773778300879978025 := by
  unfold tailWord_3747925
  simp only [CollatzResearch.WordTrace]
  refine ⟨136698054946915294474573229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91132036631276862983048819 136698054946915294474573229)
  ·
    refine ⟨51261770605093235427964961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136698054946915294474573229 51261770605093235427964961)
    ·
      refine ⟨38446327953819926570973721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51261770605093235427964961 38446327953819926570973721)
      ·
        refine ⟨28834745965364944928230291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38446327953819926570973721 28834745965364944928230291)
        ·
          refine ⟨43252118948047417392345437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28834745965364944928230291 43252118948047417392345437)
          ·
            refine ⟨16219544605517781522129539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43252118948047417392345437 16219544605517781522129539)
            ·
              refine ⟨24329316908276672283194309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16219544605517781522129539 24329316908276672283194309)
              ·
                refine ⟨4561746920301876053098933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24329316908276672283194309 4561746920301876053098933)
                ·
                  refine ⟨427663773778300879978025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4561746920301876053098933 427663773778300879978025)
                  ·
                    rfl

theorem cell22_3747925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 4, 5].length) (baseStart_3747925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3747925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3747925 prefixEnd_3747925 := by exact prefixLift 3747925
  have htrace : WordTrace (prefixWord ++ tailWord_3747925) baseStart_3747925 baseEnd_3747925 := by
    simpa [prefixWord, tailWord_3747925, baseEnd_3747925] using wordTrace_append hprefix tailTrace_3747925
  have hstable : (prefixWord ++ tailWord_3747925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747925).length < 2 ^ (prefixWord ++ tailWord_3747925).sum := by decide
  have hdescent : baseEnd_3747925 < baseStart_3747925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747972 : List Nat := [2, 3, 2, 1, 2, 1, 3, 3, 1, 4]
def baseStart_3747972 : Nat := 118140960795 + 3747972 * 2 ^ 59
def prefixEnd_3747972 : Nat := 4983230072969 + 3 ^ 40 * 3747972 * 2
def baseEnd_3747972 : Nat := 1283007410395410184008931

theorem tailTrace_3747972 : CollatzResearch.WordTrace tailWord_3747972 prefixEnd_3747972 1283007410395410184008931 := by
  unfold tailWord_3747972
  simp only [CollatzResearch.WordTrace]
  refine ⟨68349884588872510750767085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91133179451830014334356113 68349884588872510750767085)
  ·
    refine ⟨25631206720827191531537657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68349884588872510750767085 25631206720827191531537657)
    ·
      refine ⟨19223405040620393648653243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25631206720827191531537657 19223405040620393648653243)
      ·
        refine ⟨28835107560930590472979865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19223405040620393648653243 28835107560930590472979865)
        ·
          refine ⟨21626330670697942854734899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28835107560930590472979865 21626330670697942854734899)
          ·
            refine ⟨32439496006046914282102349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21626330670697942854734899 32439496006046914282102349)
            ·
              refine ⟨12164811002267592855788381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32439496006046914282102349 12164811002267592855788381)
              ·
                refine ⟨4561804125850347320920643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12164811002267592855788381 4561804125850347320920643)
                ·
                  refine ⟨6842706188775520981380965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4561804125850347320920643 6842706188775520981380965)
                  ·
                    refine ⟨1283007410395410184008931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6842706188775520981380965 1283007410395410184008931)
                    ·
                      rfl

theorem cell22_3747972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_3747972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3747972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3747972 prefixEnd_3747972 := by exact prefixLift 3747972
  have htrace : WordTrace (prefixWord ++ tailWord_3747972) baseStart_3747972 baseEnd_3747972 := by
    simpa [prefixWord, tailWord_3747972, baseEnd_3747972] using wordTrace_append hprefix tailTrace_3747972
  have hstable : (prefixWord ++ tailWord_3747972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747972).length < 2 ^ (prefixWord ++ tailWord_3747972).sum := by decide
  have hdescent : baseEnd_3747972 < baseStart_3747972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748000 : List Nat := [2, 1, 1, 4, 2, 2, 1, 2, 1, 6]
def baseStart_3748000 : Nat := 118140960795 + 3748000 * 2 ^ 59
def prefixEnd_3748000 : Nat := 4983230072969 + 3 ^ 40 * 3748000 * 2
def baseEnd_3748000 : Nat := 1283016995367627444308845

theorem tailTrace_3748000 : CollatzResearch.WordTrace tailWord_3748000 prefixEnd_3748000 1283016995367627444308845 := by
  unfold tailWord_3748000
  simp only [CollatzResearch.WordTrace]
  refine ⟨68350395210821791141776727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91133860281095721522368969 68350395210821791141776727)
  ·
    refine ⟨102525592816232686712665091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68350395210821791141776727 102525592816232686712665091)
    ·
      refine ⟨153788389224349030068997637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102525592816232686712665091 153788389224349030068997637)
      ·
        refine ⟨28835322979565443137937057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153788389224349030068997637 28835322979565443137937057)
        ·
          refine ⟨21626492234674082353452793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28835322979565443137937057 21626492234674082353452793)
          ·
            refine ⟨16219869176005561765089595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21626492234674082353452793 16219869176005561765089595)
            ·
              refine ⟨24329803764008342647634393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16219869176005561765089595 24329803764008342647634393)
              ·
                refine ⟨18247352823006256985725795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24329803764008342647634393 18247352823006256985725795)
                ·
                  refine ⟨27371029234509385478588693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18247352823006256985725795 27371029234509385478588693)
                  ·
                    refine ⟨1283016995367627444308845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27371029234509385478588693 1283016995367627444308845)
                    ·
                      rfl

theorem cell22_3748000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 1, 6].length) (baseStart_3748000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3748000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3748000 prefixEnd_3748000 := by exact prefixLift 3748000
  have htrace : WordTrace (prefixWord ++ tailWord_3748000) baseStart_3748000 baseEnd_3748000 := by
    simpa [prefixWord, tailWord_3748000, baseEnd_3748000] using wordTrace_append hprefix tailTrace_3748000
  have hstable : (prefixWord ++ tailWord_3748000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748000).length < 2 ^ (prefixWord ++ tailWord_3748000).sum := by decide
  have hdescent : baseEnd_3748000 < baseStart_3748000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748053 : List Nat := [1, 3, 2, 4, 2, 2, 2, 1, 2, 3]
def baseStart_3748053 : Nat := 118140960795 + 3748053 * 2 ^ 59
def prefixEnd_3748053 : Nat := 4983230072969 + 3 ^ 40 * 3748053 * 2
def baseEnd_3748053 : Nat := 1283035138350752972733683

theorem tailTrace_3748053 : CollatzResearch.WordTrace tailWord_3748053 prefixEnd_3748053 1283035138350752972733683 := by
  unfold tailWord_3748053
  simp only [CollatzResearch.WordTrace]
  refine ⟨136702723490451572335232813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91135148993634381556821875 136702723490451572335232813)
  ·
    refine ⟨51263521308919339625712305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136702723490451572335232813 51263521308919339625712305)
    ·
      refine ⟨38447640981689504719284229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51263521308919339625712305 38447640981689504719284229)
      ·
        refine ⟨7208932684066782134865793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38447640981689504719284229 7208932684066782134865793)
        ·
          refine ⟨5406699513050086601149345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7208932684066782134865793 5406699513050086601149345)
          ·
            refine ⟨4055024634787564950862009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5406699513050086601149345 4055024634787564950862009)
            ·
              refine ⟨3041268476090673713146507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4055024634787564950862009 3041268476090673713146507)
              ·
                refine ⟨4561902714136010569719761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3041268476090673713146507 4561902714136010569719761)
                ·
                  refine ⟨3421427035602007927289821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4561902714136010569719761 3421427035602007927289821)
                  ·
                    refine ⟨1283035138350752972733683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3421427035602007927289821 1283035138350752972733683)
                    ·
                      rfl

theorem cell22_3748053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 2, 1, 2, 3].length) (baseStart_3748053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3748053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3748053 prefixEnd_3748053 := by exact prefixLift 3748053
  have htrace : WordTrace (prefixWord ++ tailWord_3748053) baseStart_3748053 baseEnd_3748053 := by
    simpa [prefixWord, tailWord_3748053, baseEnd_3748053] using wordTrace_append hprefix tailTrace_3748053
  have hstable : (prefixWord ++ tailWord_3748053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748053).length < 2 ^ (prefixWord ++ tailWord_3748053).sum := by decide
  have hdescent : baseEnd_3748053 < baseStart_3748053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748094 : List Nat := [4, 2, 2, 1, 1, 1, 4, 2, 5]
def baseStart_3748094 : Nat := 118140960795 + 3748094 * 2 ^ 59
def prefixEnd_3748094 : Nat := 4983230072969 + 3 ^ 40 * 3748094 * 2
def baseEnd_3748094 : Nat := 427683057829547510819519

theorem tailTrace_3748094 : CollatzResearch.WordTrace tailWord_3748094 prefixEnd_3748094 427683057829547510819519 := by
  unfold tailWord_3748094
  simp only [CollatzResearch.WordTrace]
  refine ⟨17088027360412879542184417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91136145922202024224983557 17088027360412879542184417)
  ·
    refine ⟨12816020520309659656638313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17088027360412879542184417 12816020520309659656638313)
    ·
      refine ⟨9612015390232244742478735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12816020520309659656638313 9612015390232244742478735)
      ·
        refine ⟨14418023085348367113718103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9612015390232244742478735 14418023085348367113718103)
        ·
          refine ⟨21627034628022550670577155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14418023085348367113718103 21627034628022550670577155)
          ·
            refine ⟨32440551942033826005865733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21627034628022550670577155 32440551942033826005865733)
            ·
              refine ⟨6082603489131342376099825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32440551942033826005865733 6082603489131342376099825)
              ·
                refine ⟨4561952616848506782074869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6082603489131342376099825 4561952616848506782074869)
                ·
                  refine ⟨427683057829547510819519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4561952616848506782074869 427683057829547510819519)
                  ·
                    rfl

theorem cell22_3748094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_3748094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3748094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3748094 prefixEnd_3748094 := by exact prefixLift 3748094
  have htrace : WordTrace (prefixWord ++ tailWord_3748094) baseStart_3748094 baseEnd_3748094 := by
    simpa [prefixWord, tailWord_3748094, baseEnd_3748094] using wordTrace_append hprefix tailTrace_3748094
  have hstable : (prefixWord ++ tailWord_3748094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748094).length < 2 ^ (prefixWord ++ tailWord_3748094).sum := by decide
  have hdescent : baseEnd_3748094 < baseStart_3748094 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748098 : List Nat := [3, 4, 1, 1, 2, 2, 1, 4, 1, 3]
def baseStart_3748098 : Nat := 118140960795 + 3748098 * 2 ^ 59
def prefixEnd_3748098 : Nat := 4983230072969 + 3 ^ 40 * 3748098 * 2
def baseEnd_3748098 : Nat := 1283050542770387855358545

theorem tailTrace_3748098 : CollatzResearch.WordTrace tailWord_3748098 prefixEnd_3748098 1283050542770387855358545 := by
  unfold tailWord_3748098
  simp only [CollatzResearch.WordTrace]
  refine ⟨34176091193822136255155237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91136243183525696680413965 34176091193822136255155237)
  ·
    refine ⟨6408017098841650547841607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34176091193822136255155237 6408017098841650547841607)
    ·
      refine ⟨9612025648262475821762411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6408017098841650547841607 9612025648262475821762411)
      ·
        refine ⟨14418038472393713732643617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9612025648262475821762411 14418038472393713732643617)
        ·
          refine ⟨10813528854295285299482713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14418038472393713732643617 10813528854295285299482713)
          ·
            refine ⟨8110146640721463974612035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10813528854295285299482713 8110146640721463974612035)
            ·
              refine ⟨12165219961082195961918053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8110146640721463974612035 12165219961082195961918053)
              ·
                refine ⟨2280978742702911742859635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12165219961082195961918053 2280978742702911742859635)
                ·
                  refine ⟨3421468114054367614289453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2280978742702911742859635 3421468114054367614289453)
                  ·
                    refine ⟨1283050542770387855358545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3421468114054367614289453 1283050542770387855358545)
                    ·
                      rfl

theorem cell22_3748098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_3748098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3748098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3748098 prefixEnd_3748098 := by exact prefixLift 3748098
  have htrace : WordTrace (prefixWord ++ tailWord_3748098) baseStart_3748098 baseEnd_3748098 := by
    simpa [prefixWord, tailWord_3748098, baseEnd_3748098] using wordTrace_append hprefix tailTrace_3748098
  have hstable : (prefixWord ++ tailWord_3748098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748098).length < 2 ^ (prefixWord ++ tailWord_3748098).sum := by decide
  have hdescent : baseEnd_3748098 < baseStart_3748098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748152 : List Nat := [2, 1, 2, 1, 3, 1, 2, 4, 2, 4]
def baseStart_3748152 : Nat := 118140960795 + 3748152 * 2 ^ 59
def prefixEnd_3748152 : Nat := 4983230072969 + 3 ^ 40 * 3748152 * 2
def baseEnd_3748152 : Nat := 1283069028073949714508379

theorem tailTrace_3748152 : CollatzResearch.WordTrace tailWord_3748152 prefixEnd_3748152 1283069028073949714508379 := by
  unfold tailWord_3748152
  simp only [CollatzResearch.WordTrace]
  refine ⟨68353167158546456121543355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91137556211395274828724473 68353167158546456121543355)
  ·
    refine ⟨102529750737819684182315033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68353167158546456121543355 102529750737819684182315033)
    ·
      refine ⟨76897313053364763136736275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102529750737819684182315033 76897313053364763136736275)
      ·
        refine ⟨115345969580047144705104413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76897313053364763136736275 115345969580047144705104413)
        ·
          refine ⟨43254738592517679264414155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115345969580047144705104413 43254738592517679264414155)
          ·
            refine ⟨64882107888776518896621233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43254738592517679264414155 64882107888776518896621233)
            ·
              refine ⟨48661580916582389172465925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64882107888776518896621233 48661580916582389172465925)
              ·
                refine ⟨9124046421859197969837361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48661580916582389172465925 9124046421859197969837361)
                ·
                  refine ⟨6843034816394398477378021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9124046421859197969837361 6843034816394398477378021)
                  ·
                    refine ⟨1283069028073949714508379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6843034816394398477378021 1283069028073949714508379)
                    ·
                      rfl

theorem cell22_3748152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 4, 2, 4].length) (baseStart_3748152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3748152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3748152 prefixEnd_3748152 := by exact prefixLift 3748152
  have htrace : WordTrace (prefixWord ++ tailWord_3748152) baseStart_3748152 baseEnd_3748152 := by
    simpa [prefixWord, tailWord_3748152, baseEnd_3748152] using wordTrace_append hprefix tailTrace_3748152
  have hstable : (prefixWord ++ tailWord_3748152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748152).length < 2 ^ (prefixWord ++ tailWord_3748152).sum := by decide
  have hdescent : baseEnd_3748152 < baseStart_3748152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748154 : List Nat := [3, 1, 1, 1, 4, 3, 1, 1, 4, 3]
def baseStart_3748154 : Nat := 118140960795 + 3748154 * 2 ^ 59
def prefixEnd_3748154 : Nat := 4983230072969 + 3 ^ 40 * 3748154 * 2
def baseEnd_3748154 : Nat := 1283069712714822375958373

theorem tailTrace_3748154 : CollatzResearch.WordTrace tailWord_3748154 prefixEnd_3748154 1283069712714822375958373 := by
  unfold tailWord_3748154
  simp only [CollatzResearch.WordTrace]
  refine ⟨34176601815771416646164879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91137604842057111056439677 34176601815771416646164879)
  ·
    refine ⟨51264902723657124969247319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34176601815771416646164879 51264902723657124969247319)
    ·
      refine ⟨76897354085485687453870979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51264902723657124969247319 76897354085485687453870979)
      ·
        refine ⟨115346031128228531180806469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76897354085485687453870979 115346031128228531180806469)
        ·
          refine ⟨21627380836542849596401213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115346031128228531180806469 21627380836542849596401213)
          ·
            refine ⟨8110267813703568598650455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21627380836542849596401213 8110267813703568598650455)
            ·
              refine ⟨12165401720555352897975683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8110267813703568598650455 12165401720555352897975683)
              ·
                refine ⟨18248102580833029346963525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12165401720555352897975683 18248102580833029346963525)
                ·
                  refine ⟨3421519233906193002555661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18248102580833029346963525 3421519233906193002555661)
                  ·
                    refine ⟨1283069712714822375958373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3421519233906193002555661 1283069712714822375958373)
                    ·
                      rfl

theorem cell22_3748154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 4, 3].length) (baseStart_3748154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3748154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3748154 prefixEnd_3748154 := by exact prefixLift 3748154
  have htrace : WordTrace (prefixWord ++ tailWord_3748154) baseStart_3748154 baseEnd_3748154 := by
    simpa [prefixWord, tailWord_3748154, baseEnd_3748154] using wordTrace_append hprefix tailTrace_3748154
  have hstable : (prefixWord ++ tailWord_3748154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748154).length < 2 ^ (prefixWord ++ tailWord_3748154).sum := by decide
  have hdescent : baseEnd_3748154 < baseStart_3748154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748308 : List Nat := [2, 4, 1, 2, 2, 2, 2, 3, 4]
def baseStart_3748308 : Nat := 118140960795 + 3748308 * 2 ^ 59
def prefixEnd_3748308 : Nat := 4983230072969 + 3 ^ 40 * 3748308 * 2
def baseEnd_3748308 : Nat := 427707476687339102535967

theorem tailTrace_3748308 : CollatzResearch.WordTrace tailWord_3748308 prefixEnd_3748308 427707476687339102535967 := by
  unfold tailWord_3748308
  simp only [CollatzResearch.WordTrace]
  refine ⟨68356012052263875442882789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91141349403018500590510385 68356012052263875442882789)
  ·
    refine ⟨12816752259799476645540523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68356012052263875442882789 12816752259799476645540523)
    ·
      refine ⟨19225128389699214968310785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12816752259799476645540523 19225128389699214968310785)
      ·
        refine ⟨14418846292274411226233089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19225128389699214968310785 14418846292274411226233089)
        ·
          refine ⟨10814134719205808419674817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14418846292274411226233089 10814134719205808419674817)
          ·
            refine ⟨8110601039404356314756113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10814134719205808419674817 8110601039404356314756113)
            ·
              refine ⟨6082950779553267236067085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8110601039404356314756113 6082950779553267236067085)
              ·
                refine ⟨2281106542332475213525157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6082950779553267236067085 2281106542332475213525157)
                ·
                  refine ⟨427707476687339102535967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2281106542332475213525157 427707476687339102535967)
                  ·
                    rfl

theorem cell22_3748308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 3, 4].length) (baseStart_3748308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3748308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3748308 prefixEnd_3748308 := by exact prefixLift 3748308
  have htrace : WordTrace (prefixWord ++ tailWord_3748308) baseStart_3748308 baseEnd_3748308 := by
    simpa [prefixWord, tailWord_3748308, baseEnd_3748308] using wordTrace_append hprefix tailTrace_3748308
  have hstable : (prefixWord ++ tailWord_3748308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748308).length < 2 ^ (prefixWord ++ tailWord_3748308).sum := by decide
  have hdescent : baseEnd_3748308 < baseStart_3748308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748347 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 11]
def baseStart_3748347 : Nat := 118140960795 + 3748347 * 2 ^ 59
def prefixEnd_3748347 : Nat := 4983230072969 + 3 ^ 40 * 3748347 * 2
def baseEnd_3748347 : Nat := 427711926853011401960927

theorem tailTrace_3748347 : CollatzResearch.WordTrace tailWord_3748347 prefixEnd_3748347 427711926853011401960927 := by
  unfold tailWord_3748347
  simp only [CollatzResearch.WordTrace]
  refine ⟨136713446551386460546435295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91142297700924307030956863 136713446551386460546435295)
  ·
    refine ⟨205070169827079690819652943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136713446551386460546435295 205070169827079690819652943)
    ·
      refine ⟨307605254740619536229479415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205070169827079690819652943 307605254740619536229479415)
      ·
        refine ⟨461407882110929304344219123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307605254740619536229479415 461407882110929304344219123)
        ·
          refine ⟨692111823166393956516328685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 461407882110929304344219123 692111823166393956516328685)
          ·
            refine ⟨259541933687397733693623257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 692111823166393956516328685 259541933687397733693623257)
            ·
              refine ⟨194656450265548300270217443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 259541933687397733693623257 194656450265548300270217443)
              ·
                refine ⟨291984675398322450405326165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194656450265548300270217443 291984675398322450405326165)
                ·
                  refine ⟨427711926853011401960927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 291984675398322450405326165 427711926853011401960927)
                  ·
                    rfl

theorem cell22_3748347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 11].length) (baseStart_3748347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3748347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3748347 prefixEnd_3748347 := by exact prefixLift 3748347
  have htrace : WordTrace (prefixWord ++ tailWord_3748347) baseStart_3748347 baseEnd_3748347 := by
    simpa [prefixWord, tailWord_3748347, baseEnd_3748347] using wordTrace_append hprefix tailTrace_3748347
  have hstable : (prefixWord ++ tailWord_3748347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748347).length < 2 ^ (prefixWord ++ tailWord_3748347).sum := by decide
  have hdescent : baseEnd_3748347 < baseStart_3748347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748364 : List Nat := [2, 2, 1, 2, 4, 1, 1, 2, 7]
def baseStart_3748364 : Nat := 118140960795 + 3748364 * 2 ^ 59
def prefixEnd_3748364 : Nat := 4983230072969 + 3 ^ 40 * 3748364 * 2
def baseEnd_3748364 : Nat := 427713866668817276069243

theorem tailTrace_3748364 : CollatzResearch.WordTrace tailWord_3748364 prefixEnd_3748364 427713866668817276069243 := by
  unfold tailWord_3748364
  simp only [CollatzResearch.WordTrace]
  refine ⟨68357033296162436224902073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91142711061549914966536097 68357033296162436224902073)
  ·
    refine ⟨51267774972121827168676555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68357033296162436224902073 51267774972121827168676555)
    ·
      refine ⟨76901662458182740753014833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51267774972121827168676555 76901662458182740753014833)
      ·
        refine ⟨57676246843637055564761125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76901662458182740753014833 57676246843637055564761125)
        ·
          refine ⟨10814296283181947918392711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57676246843637055564761125 10814296283181947918392711)
          ·
            refine ⟨16221444424772921877589067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10814296283181947918392711 16221444424772921877589067)
            ·
              refine ⟨24332166637159382816383601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16221444424772921877589067 24332166637159382816383601)
              ·
                refine ⟨18249124977869537112287701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24332166637159382816383601 18249124977869537112287701)
                ·
                  refine ⟨427713866668817276069243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18249124977869537112287701 427713866668817276069243)
                  ·
                    rfl

theorem cell22_3748364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 7].length) (baseStart_3748364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3748364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3748364 prefixEnd_3748364 := by exact prefixLift 3748364
  have htrace : WordTrace (prefixWord ++ tailWord_3748364) baseStart_3748364 baseEnd_3748364 := by
    simpa [prefixWord, tailWord_3748364, baseEnd_3748364] using wordTrace_append hprefix tailTrace_3748364
  have hstable : (prefixWord ++ tailWord_3748364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748364).length < 2 ^ (prefixWord ++ tailWord_3748364).sum := by decide
  have hdescent : baseEnd_3748364 < baseStart_3748364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748385 : List Nat := [1, 2, 3, 2, 2, 1, 5, 2, 1, 3]
def baseStart_3748385 : Nat := 118140960795 + 3748385 * 2 ^ 59
def prefixEnd_3748385 : Nat := 4983230072969 + 3 ^ 40 * 3748385 * 2
def baseEnd_3748385 : Nat := 1283148788735614773432665

theorem tailTrace_3748385 : CollatzResearch.WordTrace tailWord_3748385 prefixEnd_3748385 1283148788735614773432665 := by
  unfold tailWord_3748385
  simp only [CollatzResearch.WordTrace]
  refine ⟨136714832525248793036318609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91143221683499195357545739 136714832525248793036318609)
  ·
    refine ⟨102536124393936594777238957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136714832525248793036318609 102536124393936594777238957)
    ·
      refine ⟨38451046647726223041464609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102536124393936594777238957 38451046647726223041464609)
      ·
        refine ⟨28838284985794667281098457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38451046647726223041464609 28838284985794667281098457)
        ·
          refine ⟨21628713739346000460823843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28838284985794667281098457 21628713739346000460823843)
          ·
            refine ⟨32443070609019000691235765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21628713739346000460823843 32443070609019000691235765)
            ·
              refine ⟨3041537869595531314803353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32443070609019000691235765 3041537869595531314803353)
              ·
                refine ⟨2281153402196648486102515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3041537869595531314803353 2281153402196648486102515)
                ·
                  refine ⟨3421730103294972729153773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2281153402196648486102515 3421730103294972729153773)
                  ·
                    refine ⟨1283148788735614773432665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3421730103294972729153773 1283148788735614773432665)
                    ·
                      rfl

theorem cell22_3748385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 5, 2, 1, 3].length) (baseStart_3748385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3748385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3748385 prefixEnd_3748385 := by exact prefixLift 3748385
  have htrace : WordTrace (prefixWord ++ tailWord_3748385) baseStart_3748385 baseEnd_3748385 := by
    simpa [prefixWord, tailWord_3748385, baseEnd_3748385] using wordTrace_append hprefix tailTrace_3748385
  have hstable : (prefixWord ++ tailWord_3748385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748385).length < 2 ^ (prefixWord ++ tailWord_3748385).sum := by decide
  have hdescent : baseEnd_3748385 < baseStart_3748385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748398 : List Nat := [4, 1, 3, 1, 3, 1, 1, 3, 5]
def baseStart_3748398 : Nat := 118140960795 + 3748398 * 2 ^ 59
def prefixEnd_3748398 : Nat := 4983230072969 + 3 ^ 40 * 3748398 * 2
def baseEnd_3748398 : Nat := 427717746300429024285875

theorem tailTrace_3748398 : CollatzResearch.WordTrace tailWord_3748398 prefixEnd_3748398 427717746300429024285875 := by
  unfold tailWord_3748398
  simp only [CollatzResearch.WordTrace]
  refine ⟨17089413334275212032067731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91143537782801130837694565 17089413334275212032067731)
  ·
    refine ⟨25634120001412818048101597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17089413334275212032067731 25634120001412818048101597)
    ·
      refine ⟨9612795000529806768038099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25634120001412818048101597 9612795000529806768038099)
      ·
        refine ⟨14419192500794710152057149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9612795000529806768038099 14419192500794710152057149)
        ·
          refine ⟨5407197187798016307021431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14419192500794710152057149 5407197187798016307021431)
          ·
            refine ⟨8110795781697024460532147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5407197187798016307021431 8110795781697024460532147)
            ·
              refine ⟨12166193672545536690798221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8110795781697024460532147 12166193672545536690798221)
              ·
                refine ⟨4562322627204576259049333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12166193672545536690798221 4562322627204576259049333)
                ·
                  refine ⟨427717746300429024285875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4562322627204576259049333 427717746300429024285875)
                  ·
                    rfl

theorem cell22_3748398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 3, 5].length) (baseStart_3748398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3748398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3748398 prefixEnd_3748398 := by exact prefixLift 3748398
  have htrace : WordTrace (prefixWord ++ tailWord_3748398) baseStart_3748398 baseEnd_3748398 := by
    simpa [prefixWord, tailWord_3748398, baseEnd_3748398] using wordTrace_append hprefix tailTrace_3748398
  have hstable : (prefixWord ++ tailWord_3748398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748398).length < 2 ^ (prefixWord ++ tailWord_3748398).sum := by decide
  have hdescent : baseEnd_3748398 < baseStart_3748398 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748409 : List Nat := [1, 2, 1, 5, 1, 1, 2, 1, 8]
def baseStart_3748409 : Nat := 118140960795 + 3748409 * 2 ^ 59
def prefixEnd_3748409 : Nat := 4983230072969 + 3 ^ 40 * 3748409 * 2
def baseEnd_3748409 : Nat := 427719001475362236944197

theorem tailTrace_3748409 : CollatzResearch.WordTrace tailWord_3748409 prefixEnd_3748409 427719001475362236944197 := by
  unfold tailWord_3748409
  simp only [CollatzResearch.WordTrace]
  refine ⟨136715707877161845135192281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91143805251441230090128187 136715707877161845135192281)
  ·
    refine ⟨102536780907871383851394211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136715707877161845135192281 102536780907871383851394211)
    ·
      refine ⟨153805171361807075777091317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102536780907871383851394211 153805171361807075777091317)
      ·
        refine ⟨14419234815169413354102311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 153805171361807075777091317 14419234815169413354102311)
        ·
          refine ⟨21628852222754120031153467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14419234815169413354102311 21628852222754120031153467)
          ·
            refine ⟨32443278334131180046730201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21628852222754120031153467 32443278334131180046730201)
            ·
              refine ⟨24332458750598385035047651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32443278334131180046730201 24332458750598385035047651)
              ·
                refine ⟨36498688125897577552571477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24332458750598385035047651 36498688125897577552571477)
                ·
                  refine ⟨427719001475362236944197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36498688125897577552571477 427719001475362236944197)
                  ·
                    rfl

theorem cell22_3748409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 8].length) (baseStart_3748409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3748409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3748409 prefixEnd_3748409 := by exact prefixLift 3748409
  have htrace : WordTrace (prefixWord ++ tailWord_3748409) baseStart_3748409 baseEnd_3748409 := by
    simpa [prefixWord, tailWord_3748409, baseEnd_3748409] using wordTrace_append hprefix tailTrace_3748409
  have hstable : (prefixWord ++ tailWord_3748409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748409).length < 2 ^ (prefixWord ++ tailWord_3748409).sum := by decide
  have hdescent : baseEnd_3748409 < baseStart_3748409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748428 : List Nat := [2, 2, 1, 3, 1, 2, 5, 1, 1, 4]
def baseStart_3748428 : Nat := 118140960795 + 3748428 * 2 ^ 59
def prefixEnd_3748428 : Nat := 4983230072969 + 3 ^ 40 * 3748428 * 2
def baseEnd_3748428 : Nat := 1283163508514376994607533

theorem tailTrace_3748428 : CollatzResearch.WordTrace tailWord_3748428 prefixEnd_3748428 1283163508514376994607533 := by
  unfold tailWord_3748428
  simp only [CollatzResearch.WordTrace]
  refine ⟨68358200432046505690066969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91144267242728674253422625 68358200432046505690066969)
  ·
    refine ⟨51268650324034879267550227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68358200432046505690066969 51268650324034879267550227)
    ·
      refine ⟨76902975486052318901325341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51268650324034879267550227 76902975486052318901325341)
      ·
        refine ⟨28838615807269619587997003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76902975486052318901325341 28838615807269619587997003)
        ·
          refine ⟨43257923710904429381995505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28838615807269619587997003 43257923710904429381995505)
          ·
            refine ⟨32443442783178322036496629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43257923710904429381995505 32443442783178322036496629)
            ·
              refine ⟨3041572760922967690921559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32443442783178322036496629 3041572760922967690921559)
              ·
                refine ⟨4562359141384451536382339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3041572760922967690921559 4562359141384451536382339)
                ·
                  refine ⟨6843538712076677304573509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4562359141384451536382339 6843538712076677304573509)
                  ·
                    refine ⟨1283163508514376994607533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6843538712076677304573509 1283163508514376994607533)
                    ·
                      rfl

theorem cell22_3748428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 5, 1, 1, 4].length) (baseStart_3748428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3748428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3748428 prefixEnd_3748428 := by exact prefixLift 3748428
  have htrace : WordTrace (prefixWord ++ tailWord_3748428) baseStart_3748428 baseEnd_3748428 := by
    simpa [prefixWord, tailWord_3748428, baseEnd_3748428] using wordTrace_append hprefix tailTrace_3748428
  have hstable : (prefixWord ++ tailWord_3748428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748428).length < 2 ^ (prefixWord ++ tailWord_3748428).sum := by decide
  have hdescent : baseEnd_3748428 < baseStart_3748428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748458 : List Nat := [3, 1, 3, 2, 1, 1, 1, 5, 2, 3]
def baseStart_3748458 : Nat := 118140960795 + 3748458 * 2 ^ 59
def prefixEnd_3748458 : Nat := 4983230072969 + 3 ^ 40 * 3748458 * 2
def baseEnd_3748458 : Nat := 1283173778127466916357441

theorem tailTrace_3748458 : CollatzResearch.WordTrace tailWord_3748458 prefixEnd_3748458 1283173778127466916357441 := by
  unfold tailWord_3748458
  simp only [CollatzResearch.WordTrace]
  refine ⟨34179373763496081625931507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91144996702656217669150685 34179373763496081625931507)
  ·
    refine ⟨51269060645244122438897261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34179373763496081625931507 51269060645244122438897261)
    ·
      refine ⟨19225897741966545914586473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51269060645244122438897261 19225897741966545914586473)
      ·
        refine ⟨14419423306474909435939855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19225897741966545914586473 14419423306474909435939855)
        ·
          refine ⟨21629134959712364153909783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14419423306474909435939855 21629134959712364153909783)
          ·
            refine ⟨32443702439568546230864675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21629134959712364153909783 32443702439568546230864675)
            ·
              refine ⟨48665553659352819346297013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32443702439568546230864675 48665553659352819346297013)
              ·
                refine ⟨4562395655564326813715345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48665553659352819346297013 4562395655564326813715345)
                ·
                  refine ⟨3421796741673245110286509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4562395655564326813715345 3421796741673245110286509)
                  ·
                    refine ⟨1283173778127466916357441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3421796741673245110286509 1283173778127466916357441)
                    ·
                      rfl

theorem cell22_3748458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 5, 2, 3].length) (baseStart_3748458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3748458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3748458 prefixEnd_3748458 := by exact prefixLift 3748458
  have htrace : WordTrace (prefixWord ++ tailWord_3748458) baseStart_3748458 baseEnd_3748458 := by
    simpa [prefixWord, tailWord_3748458, baseEnd_3748458] using wordTrace_append hprefix tailTrace_3748458
  have hstable : (prefixWord ++ tailWord_3748458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748458).length < 2 ^ (prefixWord ++ tailWord_3748458).sum := by decide
  have hdescent : baseEnd_3748458 < baseStart_3748458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748473 : List Nat := [1, 2, 1, 3, 3, 4, 1, 1, 2, 4]
def baseStart_3748473 : Nat := 118140960795 + 3748473 * 2 ^ 59
def prefixEnd_3748473 : Nat := 4983230072969 + 3 ^ 40 * 3748473 * 2
def baseEnd_3748473 : Nat := 1283178912934011877232395

theorem tailTrace_3748473 : CollatzResearch.WordTrace tailWord_3748473 prefixEnd_3748473 1283178912934011877232395 := by
  unfold tailWord_3748473
  simp only [CollatzResearch.WordTrace]
  refine ⟨136718042148929984065522073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91145361432619989377014715 136718042148929984065522073)
  ·
    refine ⟨102538531611697488049141555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136718042148929984065522073 102538531611697488049141555)
    ·
      refine ⟨153807797417546232073712333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102538531611697488049141555 153807797417546232073712333)
      ·
        refine ⟨57677924031579837027642125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153807797417546232073712333 57677924031579837027642125)
        ·
          refine ⟨21629221511842438885365797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57677924031579837027642125 21629221511842438885365797)
          ·
            refine ⟨4055479033470457291006087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21629221511842438885365797 4055479033470457291006087)
            ·
              refine ⟨6083218550205685936509131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4055479033470457291006087 6083218550205685936509131)
              ·
                refine ⟨9124827825308528904763697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6083218550205685936509131 9124827825308528904763697)
                ·
                  refine ⟨6843620868981396678572773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9124827825308528904763697 6843620868981396678572773)
                  ·
                    refine ⟨1283178912934011877232395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6843620868981396678572773 1283178912934011877232395)
                    ·
                      rfl

theorem cell22_3748473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 1, 2, 4].length) (baseStart_3748473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3748473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3748473 prefixEnd_3748473 := by exact prefixLift 3748473
  have htrace : WordTrace (prefixWord ++ tailWord_3748473) baseStart_3748473 baseEnd_3748473 := by
    simpa [prefixWord, tailWord_3748473, baseEnd_3748473] using wordTrace_append hprefix tailTrace_3748473
  have hstable : (prefixWord ++ tailWord_3748473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748473).length < 2 ^ (prefixWord ++ tailWord_3748473).sum := by decide
  have hdescent : baseEnd_3748473 < baseStart_3748473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748499 : List Nat := [1, 1, 1, 2, 1, 2, 2, 5, 7]
def baseStart_3748499 : Nat := 118140960795 + 3748499 * 2 ^ 59
def prefixEnd_3748499 : Nat := 4983230072969 + 3 ^ 40 * 3748499 * 2
def baseEnd_3748499 : Nat := 427729271088452158694105

theorem tailTrace_3748499 : CollatzResearch.WordTrace tailWord_3748499 prefixEnd_3748499 427729271088452158694105 := by
  unfold tailWord_3748499
  simp only [CollatzResearch.WordTrace]
  refine ⟨136718990446835790505968551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91145993631223860337312367 136718990446835790505968551)
  ·
    refine ⟨205078485670253685758952827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136718990446835790505968551 205078485670253685758952827)
    ·
      refine ⟨307617728505380528638429241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205078485670253685758952827 307617728505380528638429241)
      ·
        refine ⟨230713296379035396478821931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307617728505380528638429241 230713296379035396478821931)
        ·
          refine ⟨346069944568553094718232897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230713296379035396478821931 346069944568553094718232897)
          ·
            refine ⟨259552458426414821038674673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 346069944568553094718232897 259552458426414821038674673)
            ·
              refine ⟨194664343819811115779006005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 259552458426414821038674673 194664343819811115779006005)
              ·
                refine ⟨18249782233107292104281813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 194664343819811115779006005 18249782233107292104281813)
                ·
                  refine ⟨427729271088452158694105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18249782233107292104281813 427729271088452158694105)
                  ·
                    rfl

theorem cell22_3748499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 7].length) (baseStart_3748499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3748499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3748499 prefixEnd_3748499 := by exact prefixLift 3748499
  have htrace : WordTrace (prefixWord ++ tailWord_3748499) baseStart_3748499 baseEnd_3748499 := by
    simpa [prefixWord, tailWord_3748499, baseEnd_3748499] using wordTrace_append hprefix tailTrace_3748499
  have hstable : (prefixWord ++ tailWord_3748499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748499).length < 2 ^ (prefixWord ++ tailWord_3748499).sum := by decide
  have hdescent : baseEnd_3748499 < baseStart_3748499 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748503 : List Nat := [1, 1, 3, 3, 2, 1, 4, 1, 3, 3]
def baseStart_3748503 : Nat := 118140960795 + 3748503 * 2 ^ 59
def prefixEnd_3748503 : Nat := 4983230072969 + 3 ^ 40 * 3748503 * 2
def baseEnd_3748503 : Nat := 1283189182547101798982303

theorem tailTrace_3748503 : CollatzResearch.WordTrace tailWord_3748503 prefixEnd_3748503 1283189182547101798982303 := by
  unfold tailWord_3748503
  simp only [CollatzResearch.WordTrace]
  refine ⟨136719136338821299189114163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91146090892547532792742775 136719136338821299189114163)
  ·
    refine ⟨205078704508231948783671245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136719136338821299189114163 205078704508231948783671245)
    ·
      refine ⟨76904514190586980793876717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205078704508231948783671245 76904514190586980793876717)
      ·
        refine ⟨28839192821470117797703769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76904514190586980793876717 28839192821470117797703769)
        ·
          refine ⟨21629394616102588348277827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28839192821470117797703769 21629394616102588348277827)
          ·
            refine ⟨32444091924153882522416741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21629394616102588348277827 32444091924153882522416741)
            ·
              refine ⟨6083267235778852972953139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32444091924153882522416741 6083267235778852972953139)
              ·
                refine ⟨9124900853668279459429709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6083267235778852972953139 9124900853668279459429709)
                ·
                  refine ⟨3421837820125604797286141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9124900853668279459429709 3421837820125604797286141)
                  ·
                    refine ⟨1283189182547101798982303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3421837820125604797286141 1283189182547101798982303)
                    ·
                      rfl

theorem cell22_3748503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 1, 3, 3].length) (baseStart_3748503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3748503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3748503 prefixEnd_3748503 := by exact prefixLift 3748503
  have htrace : WordTrace (prefixWord ++ tailWord_3748503) baseStart_3748503 baseEnd_3748503 := by
    simpa [prefixWord, tailWord_3748503, baseEnd_3748503] using wordTrace_append hprefix tailTrace_3748503
  have hstable : (prefixWord ++ tailWord_3748503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748503).length < 2 ^ (prefixWord ++ tailWord_3748503).sum := by decide
  have hdescent : baseEnd_3748503 < baseStart_3748503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748522 : List Nat := [3, 1, 5, 2, 1, 2, 2, 6]
def baseStart_3748522 : Nat := 118140960795 + 3748522 * 2 ^ 59
def prefixEnd_3748522 : Nat := 4983230072969 + 3 ^ 40 * 3748522 * 2
def baseEnd_3748522 : Nat := 142577298515043564750805

theorem tailTrace_3748522 : CollatzResearch.WordTrace tailWord_3748522 prefixEnd_3748522 142577298515043564750805 := by
  unfold tailWord_3748522
  simp only [CollatzResearch.WordTrace]
  refine ⟨34179957331438116358513955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91146552883834976956037213 34179957331438116358513955)
  ·
    refine ⟨51269935997157174537770933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34179957331438116358513955 51269935997157174537770933)
    ·
      refine ⟨4806556499733485112916025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51269935997157174537770933 4806556499733485112916025)
      ·
        refine ⟨3604917374800113834687019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4806556499733485112916025 3604917374800113834687019)
        ·
          refine ⟨5407376062200170752030529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3604917374800113834687019 5407376062200170752030529)
          ·
            refine ⟨4055532046650128064022897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5407376062200170752030529 4055532046650128064022897)
            ·
              refine ⟨3041649034987596048017173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4055532046650128064022897 3041649034987596048017173)
              ·
                refine ⟨142577298515043564750805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3041649034987596048017173 142577298515043564750805)
                ·
                  rfl

theorem cell22_3748522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 2, 6].length) (baseStart_3748522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3748522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3748522 prefixEnd_3748522 := by exact prefixLift 3748522
  have htrace : WordTrace (prefixWord ++ tailWord_3748522) baseStart_3748522 baseEnd_3748522 := by
    simpa [prefixWord, tailWord_3748522, baseEnd_3748522] using wordTrace_append hprefix tailTrace_3748522
  have hstable : (prefixWord ++ tailWord_3748522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748522).length < 2 ^ (prefixWord ++ tailWord_3748522).sum := by decide
  have hdescent : baseEnd_3748522 < baseStart_3748522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748576 : List Nat := [2, 1, 1, 3, 1, 2, 1, 5, 1, 5]
def baseStart_3748576 : Nat := 118140960795 + 3748576 * 2 ^ 59
def prefixEnd_3748576 : Nat := 4983230072969 + 3 ^ 40 * 3748576 * 2
def baseEnd_3748576 : Nat := 1283214171938953941907079

theorem tailTrace_3748576 : CollatzResearch.WordTrace tailWord_3748576 prefixEnd_3748576 1283214171938953941907079 := by
  unfold tailWord_3748576
  simp only [CollatzResearch.WordTrace]
  refine ⟨68360899433778416328260791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91147865911704555104347721 68360899433778416328260791)
  ·
    refine ⟨102541349150667624492391187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68360899433778416328260791 102541349150667624492391187)
    ·
      refine ⟨153812023726001436738586781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102541349150667624492391187 153812023726001436738586781)
      ·
        refine ⟨57679508897250538776970043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153812023726001436738586781 57679508897250538776970043)
        ·
          refine ⟨86519263345875808165455065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57679508897250538776970043 86519263345875808165455065)
          ·
            refine ⟨64889447509406856124091299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86519263345875808165455065 64889447509406856124091299)
            ·
              refine ⟨97334171264110284186136949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64889447509406856124091299 97334171264110284186136949)
              ·
                refine ⟨9125078556010339142450339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97334171264110284186136949 9125078556010339142450339)
                ·
                  refine ⟨13687617834015508713675509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9125078556010339142450339 13687617834015508713675509)
                  ·
                    refine ⟨1283214171938953941907079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13687617834015508713675509 1283214171938953941907079)
                    ·
                      rfl

theorem cell22_3748576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 5, 1, 5].length) (baseStart_3748576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3748576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3748576 prefixEnd_3748576 := by exact prefixLift 3748576
  have htrace : WordTrace (prefixWord ++ tailWord_3748576) baseStart_3748576 baseEnd_3748576 := by
    simpa [prefixWord, tailWord_3748576, baseEnd_3748576] using wordTrace_append hprefix tailTrace_3748576
  have hstable : (prefixWord ++ tailWord_3748576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748576).length < 2 ^ (prefixWord ++ tailWord_3748576).sum := by decide
  have hdescent : baseEnd_3748576 < baseStart_3748576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748580 : List Nat := [2, 3, 1, 1, 1, 6, 1, 2, 1, 4]
def baseStart_3748580 : Nat := 118140960795 + 3748580 * 2 ^ 59
def prefixEnd_3748580 : Nat := 4983230072969 + 3 ^ 40 * 3748580 * 2
def baseEnd_3748580 : Nat := 1283215541220699264807067

theorem tailTrace_3748580 : CollatzResearch.WordTrace tailWord_3748580 prefixEnd_3748580 1283215541220699264807067 := by
  unfold tailWord_3748580
  simp only [CollatzResearch.WordTrace]
  refine ⟨68360972379771170669833597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91147963173028227559778129 68360972379771170669833597)
  ·
    refine ⟨25635364642414189001187599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68360972379771170669833597 25635364642414189001187599)
    ·
      refine ⟨38453046963621283501781399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25635364642414189001187599 38453046963621283501781399)
      ·
        refine ⟨57679570445431925252672099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38453046963621283501781399 57679570445431925252672099)
        ·
          refine ⟨86519355668147887879008149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57679570445431925252672099 86519355668147887879008149)
          ·
            refine ⟨4055594796944432244328507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 86519355668147887879008149 4055594796944432244328507)
            ·
              refine ⟨6083392195416648366492761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4055594796944432244328507 6083392195416648366492761)
              ·
                refine ⟨4562544146562486274869571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6083392195416648366492761 4562544146562486274869571)
                ·
                  refine ⟨6843816219843729412304357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4562544146562486274869571 6843816219843729412304357)
                  ·
                    refine ⟨1283215541220699264807067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6843816219843729412304357 1283215541220699264807067)
                    ·
                      rfl

theorem cell22_3748580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 2, 1, 4].length) (baseStart_3748580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3748580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3748580 prefixEnd_3748580 := by exact prefixLift 3748580
  have htrace : WordTrace (prefixWord ++ tailWord_3748580) baseStart_3748580 baseEnd_3748580 := by
    simpa [prefixWord, tailWord_3748580, baseEnd_3748580] using wordTrace_append hprefix tailTrace_3748580
  have hstable : (prefixWord ++ tailWord_3748580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748580).length < 2 ^ (prefixWord ++ tailWord_3748580).sum := by decide
  have hdescent : baseEnd_3748580 < baseStart_3748580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748706 : List Nat := [3, 3, 2, 1, 3, 2, 1, 3, 1, 3]
def baseStart_3748706 : Nat := 118140960795 + 3748706 * 2 ^ 59
def prefixEnd_3748706 : Nat := 4983230072969 + 3 ^ 40 * 3748706 * 2
def baseEnd_3748706 : Nat := 1283258673595676936156681

theorem tailTrace_3748706 : CollatzResearch.WordTrace tailWord_3748706 prefixEnd_3748706 1283258673595676936156681 := by
  unfold tailWord_3748706
  simp only [CollatzResearch.WordTrace]
  refine ⟨34181635089271466214688493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91151026904723909905835981 34181635089271466214688493)
  ·
    refine ⟨12818113158476799830508185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34181635089271466214688493 12818113158476799830508185)
    ·
      refine ⟨9613584868857599872881139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12818113158476799830508185 9613584868857599872881139)
      ·
        refine ⟨14420377303286399809321709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9613584868857599872881139 14420377303286399809321709)
        ·
          refine ⟨5407641488732399928495641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14420377303286399809321709 5407641488732399928495641)
          ·
            refine ⟨4055731116549299946371731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5407641488732399928495641 4055731116549299946371731)
            ·
              refine ⟨6083596674823949919557597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4055731116549299946371731 6083596674823949919557597)
              ·
                refine ⟨2281348753058981219834099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6083596674823949919557597 2281348753058981219834099)
                ·
                  refine ⟨3422023129588471829751149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2281348753058981219834099 3422023129588471829751149)
                  ·
                    refine ⟨1283258673595676936156681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3422023129588471829751149 1283258673595676936156681)
                    ·
                      rfl

theorem cell22_3748706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_3748706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3748706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3748706 prefixEnd_3748706 := by exact prefixLift 3748706
  have htrace : WordTrace (prefixWord ++ tailWord_3748706) baseStart_3748706 baseEnd_3748706 := by
    simpa [prefixWord, tailWord_3748706, baseEnd_3748706] using wordTrace_append hprefix tailTrace_3748706
  have hstable : (prefixWord ++ tailWord_3748706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748706).length < 2 ^ (prefixWord ++ tailWord_3748706).sum := by decide
  have hdescent : baseEnd_3748706 < baseStart_3748706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748775 : List Nat := [1, 1, 6, 1, 4, 9]
def baseStart_3748775 : Nat := 118140960795 + 3748775 * 2 ^ 59
def prefixEnd_3748775 : Nat := 4983230072969 + 3 ^ 40 * 3748775 * 2
def baseEnd_3748775 : Nat := 15842991280318317977549

theorem tailTrace_3748775 : CollatzResearch.WordTrace tailWord_3748775 prefixEnd_3748775 15842991280318317977549 := by
  unfold tailWord_3748775
  simp only [CollatzResearch.WordTrace]
  refine ⟨136729056993835889643015779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91152704662557259762010519 136729056993835889643015779)
  ·
    refine ⟨205093585490753834464523669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136729056993835889643015779 205093585490753834464523669)
    ·
      refine ⟨9613761819879085990524547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 205093585490753834464523669 9613761819879085990524547)
      ·
        refine ⟨14420642729818628985786821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9613761819879085990524547 14420642729818628985786821)
        ·
          refine ⟨2703870511840992934835029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14420642729818628985786821 2703870511840992934835029)
          ·
            refine ⟨15842991280318317977549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2703870511840992934835029 15842991280318317977549)
            ·
              rfl

theorem cell22_3748775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 9].length) (baseStart_3748775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3748775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3748775 prefixEnd_3748775 := by exact prefixLift 3748775
  have htrace : WordTrace (prefixWord ++ tailWord_3748775) baseStart_3748775 baseEnd_3748775 := by
    simpa [prefixWord, tailWord_3748775, baseEnd_3748775] using wordTrace_append hprefix tailTrace_3748775
  have hstable : (prefixWord ++ tailWord_3748775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748775).length < 2 ^ (prefixWord ++ tailWord_3748775).sum := by decide
  have hdescent : baseEnd_3748775 < baseStart_3748775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748824 : List Nat := [2, 1, 2, 2, 2, 4, 2, 3, 1, 3]
def baseStart_3748824 : Nat := 118140960795 + 3748824 * 2 ^ 59
def prefixEnd_3748824 : Nat := 4983230072969 + 3 ^ 40 * 3748824 * 2
def baseEnd_3748824 : Nat := 1283299067407163961706319

theorem tailTrace_3748824 : CollatzResearch.WordTrace tailWord_3748824 prefixEnd_3748824 1283299067407163961706319 := by
  unfold tailWord_3748824
  simp only [CollatzResearch.WordTrace]
  refine ⟨68365422085329185505774763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91153896113772247341033017 68365422085329185505774763)
  ·
    refine ⟨102548133127993778258662145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68365422085329185505774763 102548133127993778258662145)
    ·
      refine ⟨76911099845995333693996609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102548133127993778258662145 76911099845995333693996609)
      ·
        refine ⟨57683324884496500270497457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76911099845995333693996609 57683324884496500270497457)
        ·
          refine ⟨43262493663372375202873093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57683324884496500270497457 43262493663372375202873093)
          ·
            refine ⟨8111717561882320350538705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43262493663372375202873093 8111717561882320350538705)
            ·
              refine ⟨6083788171411740262904029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8111717561882320350538705 6083788171411740262904029)
              ·
                refine ⟨2281420564279402598589011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6083788171411740262904029 2281420564279402598589011)
                ·
                  refine ⟨3422130846419103897883517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2281420564279402598589011 3422130846419103897883517)
                  ·
                    refine ⟨1283299067407163961706319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3422130846419103897883517 1283299067407163961706319)
                    ·
                      rfl

theorem cell22_3748824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 3, 1, 3].length) (baseStart_3748824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3748824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3748824 prefixEnd_3748824 := by exact prefixLift 3748824
  have htrace : WordTrace (prefixWord ++ tailWord_3748824) baseStart_3748824 baseEnd_3748824 := by
    simpa [prefixWord, tailWord_3748824, baseEnd_3748824] using wordTrace_append hprefix tailTrace_3748824
  have hstable : (prefixWord ++ tailWord_3748824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748824).length < 2 ^ (prefixWord ++ tailWord_3748824).sum := by decide
  have hdescent : baseEnd_3748824 < baseStart_3748824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748837 : List Nat := [1, 3, 1, 6, 1, 1, 1, 1, 7]
def baseStart_3748837 : Nat := 118140960795 + 3748837 * 2 ^ 59
def prefixEnd_3748837 : Nat := 4983230072969 + 3 ^ 40 * 3748837 * 2
def baseEnd_3748837 : Nat := 427767839190945420377093

theorem tailTrace_3748837 : CollatzResearch.WordTrace tailWord_3748837 prefixEnd_3748837 427767839190945420377093 := by
  unfold tailWord_3748837
  simp only [CollatzResearch.WordTrace]
  refine ⟨136731318319611274231772765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91154212213074182821181843 136731318319611274231772765)
  ·
    refine ⟨51274244369854227836914787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136731318319611274231772765 51274244369854227836914787)
    ·
      refine ⟨76911366554781341755372181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51274244369854227836914787 76911366554781341755372181)
      ·
        refine ⟨3605220307255375394783071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 76911366554781341755372181 3605220307255375394783071)
        ·
          refine ⟨5407830460883063092174607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3605220307255375394783071 5407830460883063092174607)
          ·
            refine ⟨8111745691324594638261911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5407830460883063092174607 8111745691324594638261911)
            ·
              refine ⟨12167618536986891957392867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8111745691324594638261911 12167618536986891957392867)
              ·
                refine ⟨18251427805480337936089301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12167618536986891957392867 18251427805480337936089301)
                ·
                  refine ⟨427767839190945420377093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18251427805480337936089301 427767839190945420377093)
                  ·
                    rfl

theorem cell22_3748837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 7].length) (baseStart_3748837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3748837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3748837 prefixEnd_3748837 := by exact prefixLift 3748837
  have htrace : WordTrace (prefixWord ++ tailWord_3748837) baseStart_3748837 baseEnd_3748837 := by
    simpa [prefixWord, tailWord_3748837, baseEnd_3748837] using wordTrace_append hprefix tailTrace_3748837
  have hstable : (prefixWord ++ tailWord_3748837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748837).length < 2 ^ (prefixWord ++ tailWord_3748837).sum := by decide
  have hdescent : baseEnd_3748837 < baseStart_3748837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748854 : List Nat := [5, 1, 1, 1, 3, 2, 3, 1, 5]
def baseStart_3748854 : Nat := 118140960795 + 3748854 * 2 ^ 59
def prefixEnd_3748854 : Nat := 4983230072969 + 3 ^ 40 * 3748854 * 2
def baseEnd_3748854 : Nat := 427769779006751294485409

theorem tailTrace_3748854 : CollatzResearch.WordTrace tailWord_3748854 prefixEnd_3748854 427769779006751294485409 := by
  unfold tailWord_3748854
  simp only [CollatzResearch.WordTrace]
  refine ⟨8545746147534355383446351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91154625573699790756761077 8545746147534355383446351)
  ·
    refine ⟨12818619221301533075169527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8545746147534355383446351 12818619221301533075169527)
    ·
      refine ⟨19227928831952299612754291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12818619221301533075169527 19227928831952299612754291)
      ·
        refine ⟨28841893247928449419131437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19227928831952299612754291 28841893247928449419131437)
        ·
          refine ⟨10815709967973168532174289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28841893247928449419131437 10815709967973168532174289)
          ·
            refine ⟨8111782475979876399130717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10815709967973168532174289 8111782475979876399130717)
            ·
              refine ⟨3041918428492453649674019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8111782475979876399130717 3041918428492453649674019)
              ·
                refine ⟨4562877642738680474511029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3041918428492453649674019 4562877642738680474511029)
                ·
                  refine ⟨427769779006751294485409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4562877642738680474511029 427769779006751294485409)
                  ·
                    rfl

theorem cell22_3748854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 3, 1, 5].length) (baseStart_3748854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3748854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3748854 prefixEnd_3748854 := by exact prefixLift 3748854
  have htrace : WordTrace (prefixWord ++ tailWord_3748854) baseStart_3748854 baseEnd_3748854 := by
    simpa [prefixWord, tailWord_3748854, baseEnd_3748854] using wordTrace_append hprefix tailTrace_3748854
  have hstable : (prefixWord ++ tailWord_3748854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748854).length < 2 ^ (prefixWord ++ tailWord_3748854).sum := by decide
  have hdescent : baseEnd_3748854 < baseStart_3748854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748865 : List Nat := [1, 2, 4, 1, 2, 2, 2, 2, 6]
def baseStart_3748865 : Nat := 118140960795 + 3748865 * 2 ^ 59
def prefixEnd_3748865 : Nat := 4983230072969 + 3 ^ 40 * 3748865 * 2
def baseEnd_3748865 : Nat := 427771034181684507143731

theorem tailTrace_3748865 : CollatzResearch.WordTrace tailWord_3748865 prefixEnd_3748865 427771034181684507143731 := by
  unfold tailWord_3748865
  simp only [CollatzResearch.WordTrace]
  refine ⟨136732339563509835013792049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91154893042339890009194699 136732339563509835013792049)
  ·
    refine ⟨102549254672632376260344037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136732339563509835013792049 102549254672632376260344037)
    ·
      refine ⟨19227985251118570548814507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102549254672632376260344037 19227985251118570548814507)
      ·
        refine ⟨28841977876677855823221761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19227985251118570548814507 28841977876677855823221761)
        ·
          refine ⟨21631483407508391867416321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28841977876677855823221761 21631483407508391867416321)
          ·
            refine ⟨16223612555631293900562241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21631483407508391867416321 16223612555631293900562241)
            ·
              refine ⟨12167709416723470425421681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16223612555631293900562241 12167709416723470425421681)
              ·
                refine ⟨9125782062542602819066261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12167709416723470425421681 9125782062542602819066261)
                ·
                  refine ⟨427771034181684507143731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9125782062542602819066261 427771034181684507143731)
                  ·
                    rfl

theorem cell22_3748865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 2, 6].length) (baseStart_3748865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3748865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3748865 prefixEnd_3748865 := by exact prefixLift 3748865
  have htrace : WordTrace (prefixWord ++ tailWord_3748865) baseStart_3748865 baseEnd_3748865 := by
    simpa [prefixWord, tailWord_3748865, baseEnd_3748865] using wordTrace_append hprefix tailTrace_3748865
  have hstable : (prefixWord ++ tailWord_3748865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748865).length < 2 ^ (prefixWord ++ tailWord_3748865).sum := by decide
  have hdescent : baseEnd_3748865 < baseStart_3748865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748895 : List Nat := [1, 1, 2, 4, 1, 3, 1, 1, 4, 4]
def baseStart_3748895 : Nat := 118140960795 + 3748895 * 2 ^ 59
def prefixEnd_3748895 : Nat := 4983230072969 + 3 ^ 40 * 3748895 * 2
def baseEnd_3748895 : Nat := 1283323372158143443181101

theorem tailTrace_3748895 : CollatzResearch.WordTrace tailWord_3748895 prefixEnd_3748895 1283323372158143443181101 := by
  unfold tailWord_3748895
  simp only [CollatzResearch.WordTrace]
  refine ⟨136733433753401150137384139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91155622502267433424922759 136733433753401150137384139)
  ·
    refine ⟨205100150630101725206076209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136733433753401150137384139 205100150630101725206076209)
    ·
      refine ⟨153825112972576293904557157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205100150630101725206076209 153825112972576293904557157)
      ·
        refine ⟨28842208682358055107104467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153825112972576293904557157 28842208682358055107104467)
        ·
          refine ⟨43263313023537082660656701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28842208682358055107104467 43263313023537082660656701)
          ·
            refine ⟨16223742383826405997746263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43263313023537082660656701 16223742383826405997746263)
            ·
              refine ⟨24335613575739608996619395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16223742383826405997746263 24335613575739608996619395)
              ·
                refine ⟨36503420363609413494929093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24335613575739608996619395 36503420363609413494929093)
                ·
                  refine ⟨6844391318176765030299205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36503420363609413494929093 6844391318176765030299205)
                  ·
                    refine ⟨1283323372158143443181101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6844391318176765030299205 1283323372158143443181101)
                    ·
                      rfl

theorem cell22_3748895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 4, 4].length) (baseStart_3748895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3748895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3748895 prefixEnd_3748895 := by exact prefixLift 3748895
  have htrace : WordTrace (prefixWord ++ tailWord_3748895) baseStart_3748895 baseEnd_3748895 := by
    simpa [prefixWord, tailWord_3748895, baseEnd_3748895] using wordTrace_append hprefix tailTrace_3748895
  have hstable : (prefixWord ++ tailWord_3748895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748895).length < 2 ^ (prefixWord ++ tailWord_3748895).sum := by decide
  have hdescent : baseEnd_3748895 < baseStart_3748895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748897 : List Nat := [1, 2, 3, 2, 3, 1, 2, 1, 4, 3]
def baseStart_3748897 : Nat := 118140960795 + 3748897 * 2 ^ 59
def prefixEnd_3748897 : Nat := 4983230072969 + 3 ^ 40 * 3748897 * 2
def baseEnd_3748897 : Nat := 1283324056799016104631095

theorem tailTrace_3748897 : CollatzResearch.WordTrace tailWord_3748897 prefixEnd_3748897 1283324056799016104631095 := by
  unfold tailWord_3748897
  simp only [CollatzResearch.WordTrace]
  refine ⟨136733506699393904478956945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91155671132929269652637963 136733506699393904478956945)
  ·
    refine ⟨102550130024545428359217709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136733506699393904478956945 102550130024545428359217709)
    ·
      refine ⟨38456298759204535634706641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102550130024545428359217709 38456298759204535634706641)
      ·
        refine ⟨28842224069403401726029981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38456298759204535634706641 28842224069403401726029981)
        ·
          refine ⟨10815834026026275647261243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28842224069403401726029981 10815834026026275647261243)
          ·
            refine ⟨16223751039039413470891865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10815834026026275647261243 16223751039039413470891865)
            ·
              refine ⟨12167813279279560103168899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16223751039039413470891865 12167813279279560103168899)
              ·
                refine ⟨18251719918919340154753349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12167813279279560103168899 18251719918919340154753349)
                ·
                  refine ⟨3422197484797376279016253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18251719918919340154753349 3422197484797376279016253)
                  ·
                    refine ⟨1283324056799016104631095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3422197484797376279016253 1283324056799016104631095)
                    ·
                      rfl

theorem cell22_3748897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 4, 3].length) (baseStart_3748897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3748897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3748897 prefixEnd_3748897 := by exact prefixLift 3748897
  have htrace : WordTrace (prefixWord ++ tailWord_3748897) baseStart_3748897 baseEnd_3748897 := by
    simpa [prefixWord, tailWord_3748897, baseEnd_3748897] using wordTrace_append hprefix tailTrace_3748897
  have hstable : (prefixWord ++ tailWord_3748897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748897).length < 2 ^ (prefixWord ++ tailWord_3748897).sum := by decide
  have hdescent : baseEnd_3748897 < baseStart_3748897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748899 : List Nat := [1, 1, 1, 4, 3, 3, 3, 2, 4]
def baseStart_3748899 : Nat := 118140960795 + 3748899 * 2 ^ 59
def prefixEnd_3748899 : Nat := 4983230072969 + 3 ^ 40 * 3748899 * 2
def baseEnd_3748899 : Nat := 427774913813296255360363

theorem tailTrace_3748899 : CollatzResearch.WordTrace tailWord_3748899 prefixEnd_3748899 427774913813296255360363 := by
  unfold tailWord_3748899
  simp only [CollatzResearch.WordTrace]
  refine ⟨136733579645386658820529751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91155719763591105880353167 136733579645386658820529751)
  ·
    refine ⟨205100369468079988230794627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136733579645386658820529751 205100369468079988230794627)
    ·
      refine ⟨307650554202119982346191941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205100369468079988230794627 307650554202119982346191941)
      ·
        refine ⟨57684478912897496689910989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 307650554202119982346191941 57684478912897496689910989)
        ·
          refine ⟨21631679592336561258716621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57684478912897496689910989 21631679592336561258716621)
          ·
            refine ⟨8111879847126210472018733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21631679592336561258716621 8111879847126210472018733)
            ·
              refine ⟨3041954942672328927007025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8111879847126210472018733 3041954942672328927007025)
              ·
                refine ⟨2281466207004246695255269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3041954942672328927007025 2281466207004246695255269)
                ·
                  refine ⟨427774913813296255360363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2281466207004246695255269 427774913813296255360363)
                  ·
                    rfl

theorem cell22_3748899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 3, 2, 4].length) (baseStart_3748899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3748899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3748899 prefixEnd_3748899 := by exact prefixLift 3748899
  have htrace : WordTrace (prefixWord ++ tailWord_3748899) baseStart_3748899 baseEnd_3748899 := by
    simpa [prefixWord, tailWord_3748899, baseEnd_3748899] using wordTrace_append hprefix tailTrace_3748899
  have hstable : (prefixWord ++ tailWord_3748899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748899).length < 2 ^ (prefixWord ++ tailWord_3748899).sum := by decide
  have hdescent : baseEnd_3748899 < baseStart_3748899 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748929 : List Nat := [1, 2, 5, 1, 3, 1, 2, 1, 2, 4]
def baseStart_3748929 : Nat := 118140960795 + 3748929 * 2 ^ 59
def prefixEnd_3748929 : Nat := 4983230072969 + 3 ^ 40 * 3748929 * 2
def baseEnd_3748929 : Nat := 1283335011052978687830997

theorem tailTrace_3748929 : CollatzResearch.WordTrace tailWord_3748929 prefixEnd_3748929 1283335011052978687830997 := by
  unfold tailWord_3748929
  simp only [CollatzResearch.WordTrace]
  refine ⟨136734673835277973944121841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91156449223518649296081227 136734673835277973944121841)
  ·
    refine ⟨102551005376458480458091381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136734673835277973944121841 102551005376458480458091381)
    ·
      refine ⟨9614156754042982542946067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102551005376458480458091381 9614156754042982542946067)
      ·
        refine ⟨14421235131064473814419101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9614156754042982542946067 14421235131064473814419101)
        ·
          refine ⟨5407963174149177680407163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14421235131064473814419101 5407963174149177680407163)
          ·
            refine ⟨8111944761223766520610745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5407963174149177680407163 8111944761223766520610745)
            ·
              refine ⟨6083958570917824890458059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8111944761223766520610745 6083958570917824890458059)
              ·
                refine ⟨9125937856376737335687089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6083958570917824890458059 9125937856376737335687089)
                ·
                  refine ⟨6844453392282553001765317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9125937856376737335687089 6844453392282553001765317)
                  ·
                    refine ⟨1283335011052978687830997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6844453392282553001765317 1283335011052978687830997)
                    ·
                      rfl

theorem cell22_3748929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_3748929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3748929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3748929 prefixEnd_3748929 := by exact prefixLift 3748929
  have htrace : WordTrace (prefixWord ++ tailWord_3748929) baseStart_3748929 baseEnd_3748929 := by
    simpa [prefixWord, tailWord_3748929, baseEnd_3748929] using wordTrace_append hprefix tailTrace_3748929
  have hstable : (prefixWord ++ tailWord_3748929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748929).length < 2 ^ (prefixWord ++ tailWord_3748929).sum := by decide
  have hdescent : baseEnd_3748929 < baseStart_3748929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748950 : List Nat := [5, 2, 2, 1, 2, 2, 2, 2, 4]
def baseStart_3748950 : Nat := 118140960795 + 3748950 * 2 ^ 59
def prefixEnd_3748950 : Nat := 4983230072969 + 3 ^ 40 * 3748950 * 2
def baseEnd_3748950 : Nat := 427780733260713877685311

theorem tailTrace_3748950 : CollatzResearch.WordTrace tailWord_3748950 prefixEnd_3748950 427780733260713877685311 := by
  unfold tailWord_3748950
  simp only [CollatzResearch.WordTrace]
  refine ⟨8545964985512618408164769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91156959845467929687090869 8545964985512618408164769)
  ·
    refine ⟨6409473739134463806123577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8545964985512618408164769 6409473739134463806123577)
    ·
      refine ⟨4807105304350847854592683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6409473739134463806123577 4807105304350847854592683)
      ·
        refine ⟨7210657956526271781889025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4807105304350847854592683 7210657956526271781889025)
        ·
          refine ⟨5407993467394703836416769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7210657956526271781889025 5407993467394703836416769)
          ·
            refine ⟨4055995100546027877312577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5407993467394703836416769 4055995100546027877312577)
            ·
              refine ⟨3041996325409520907984433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4055995100546027877312577 3041996325409520907984433)
              ·
                refine ⟨2281497244057140680988325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3041996325409520907984433 2281497244057140680988325)
                ·
                  refine ⟨427780733260713877685311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2281497244057140680988325 427780733260713877685311)
                  ·
                    rfl

theorem cell22_3748950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_3748950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3748950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3748950 prefixEnd_3748950 := by exact prefixLift 3748950
  have htrace : WordTrace (prefixWord ++ tailWord_3748950) baseStart_3748950 baseEnd_3748950 := by
    simpa [prefixWord, tailWord_3748950, baseEnd_3748950] using wordTrace_append hprefix tailTrace_3748950
  have hstable : (prefixWord ++ tailWord_3748950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748950).length < 2 ^ (prefixWord ++ tailWord_3748950).sum := by decide
  have hdescent : baseEnd_3748950 < baseStart_3748950 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748959 : List Nat := [1, 1, 2, 3, 1, 1, 5, 4, 1, 3]
def baseStart_3748959 : Nat := 118140960795 + 3748959 * 2 ^ 59
def prefixEnd_3748959 : Nat := 4983230072969 + 3 ^ 40 * 3748959 * 2
def baseEnd_3748959 : Nat := 1283345280666068609580905

theorem tailTrace_3748959 : CollatzResearch.WordTrace tailWord_3748959 prefixEnd_3748959 1283345280666068609580905 := by
  unfold tailWord_3748959
  simp only [CollatzResearch.WordTrace]
  refine ⟨136735768025169289067713931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91157178683446192711809287 136735768025169289067713931)
  ·
    refine ⟨205103652037753933601570897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136735768025169289067713931 205103652037753933601570897)
    ·
      refine ⟨153827739028315450201178173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205103652037753933601570897 153827739028315450201178173)
      ·
        refine ⟨57685402135618293825441815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153827739028315450201178173 57685402135618293825441815)
        ·
          refine ⟨86528103203427440738162723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57685402135618293825441815 86528103203427440738162723)
          ·
            refine ⟨129792154805141161107244085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86528103203427440738162723 129792154805141161107244085)
            ·
              refine ⟨12168014512981983853804133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 129792154805141161107244085 12168014512981983853804133)
              ·
                refine ⟨2281502721184121972588275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12168014512981983853804133 2281502721184121972588275)
                ·
                  refine ⟨3422254081776182958882413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2281502721184121972588275 3422254081776182958882413)
                  ·
                    refine ⟨1283345280666068609580905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3422254081776182958882413 1283345280666068609580905)
                    ·
                      rfl

theorem cell22_3748959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 4, 1, 3].length) (baseStart_3748959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3748959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3748959 prefixEnd_3748959 := by exact prefixLift 3748959
  have htrace : WordTrace (prefixWord ++ tailWord_3748959) baseStart_3748959 baseEnd_3748959 := by
    simpa [prefixWord, tailWord_3748959, baseEnd_3748959] using wordTrace_append hprefix tailTrace_3748959
  have hstable : (prefixWord ++ tailWord_3748959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748959).length < 2 ^ (prefixWord ++ tailWord_3748959).sum := by decide
  have hdescent : baseEnd_3748959 < baseStart_3748959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749034 : List Nat := [3, 1, 5, 1, 1, 1, 2, 2, 6]
def baseStart_3749034 : Nat := 118140960795 + 3749034 * 2 ^ 59
def prefixEnd_3749034 : Nat := 4983230072969 + 3 ^ 40 * 3749034 * 2
def baseEnd_3749034 : Nat := 427790318232931137985225

theorem tailTrace_3749034 : CollatzResearch.WordTrace tailWord_3749034 prefixEnd_3749034 427790318232931137985225 := by
  unfold tailWord_3749034
  simp only [CollatzResearch.WordTrace]
  refine ⟨34184625874974394219173539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91159002333265051251129437 34184625874974394219173539)
  ·
    refine ⟨51276938812461591328760309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34184625874974394219173539 51276938812461591328760309)
    ·
      refine ⟨4807213013668274187071279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51276938812461591328760309 4807213013668274187071279)
      ·
        refine ⟨7210819520502411280606919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4807213013668274187071279 7210819520502411280606919)
        ·
          refine ⟨10816229280753616920910379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7210819520502411280606919 10816229280753616920910379)
          ·
            refine ⟨16224343921130425381365569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10816229280753616920910379 16224343921130425381365569)
            ·
              refine ⟨12168257940847819036024177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16224343921130425381365569 12168257940847819036024177)
              ·
                refine ⟨9126193455635864277018133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12168257940847819036024177 9126193455635864277018133)
                ·
                  refine ⟨427790318232931137985225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9126193455635864277018133 427790318232931137985225)
                  ·
                    rfl

theorem cell22_3749034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 2, 6].length) (baseStart_3749034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3749034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3749034 prefixEnd_3749034 := by exact prefixLift 3749034
  have htrace : WordTrace (prefixWord ++ tailWord_3749034) baseStart_3749034 baseEnd_3749034 := by
    simpa [prefixWord, tailWord_3749034, baseEnd_3749034] using wordTrace_append hprefix tailTrace_3749034
  have hstable : (prefixWord ++ tailWord_3749034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749034).length < 2 ^ (prefixWord ++ tailWord_3749034).sum := by decide
  have hdescent : baseEnd_3749034 < baseStart_3749034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749047 : List Nat := [1, 1, 3, 1, 4, 1, 2, 3, 2, 4]
def baseStart_3749047 : Nat := 118140960795 + 3749047 * 2 ^ 59
def prefixEnd_3749047 : Nat := 4983230072969 + 3 ^ 40 * 3749047 * 2
def baseEnd_3749047 : Nat := 1283375404864465713380635

theorem tailTrace_3749047 : CollatzResearch.WordTrace tailWord_3749047 prefixEnd_3749047 1283375404864465713380635 := by
  unfold tailWord_3749047
  simp only [CollatzResearch.WordTrace]
  refine ⟨136738977648850480096917395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91159318432566986731278263 136738977648850480096917395)
  ·
    refine ⟨205108466473275720145376093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136738977648850480096917395 205108466473275720145376093)
    ·
      refine ⟨76915674927478395054516035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205108466473275720145376093 76915674927478395054516035)
      ·
        refine ⟨115373512391217592581774053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76915674927478395054516035 115373512391217592581774053)
        ·
          refine ⟨21632533573353298609082635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115373512391217592581774053 21632533573353298609082635)
          ·
            refine ⟨32448800360029947913623953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21632533573353298609082635 32448800360029947913623953)
            ·
              refine ⟨24336600270022460935217965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32448800360029947913623953 24336600270022460935217965)
              ·
                refine ⟨9126225101258422850706737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24336600270022460935217965 9126225101258422850706737)
                ·
                  refine ⟨6844668825943817138030053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9126225101258422850706737 6844668825943817138030053)
                  ·
                    refine ⟨1283375404864465713380635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6844668825943817138030053 1283375404864465713380635)
                    ·
                      rfl

theorem cell22_3749047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 3, 2, 4].length) (baseStart_3749047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3749047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3749047 prefixEnd_3749047 := by exact prefixLift 3749047
  have htrace : WordTrace (prefixWord ++ tailWord_3749047) baseStart_3749047 baseEnd_3749047 := by
    simpa [prefixWord, tailWord_3749047, baseEnd_3749047] using wordTrace_append hprefix tailTrace_3749047
  have hstable : (prefixWord ++ tailWord_3749047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749047).length < 2 ^ (prefixWord ++ tailWord_3749047).sum := by decide
  have hdescent : baseEnd_3749047 < baseStart_3749047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749075 : List Nat := [1, 1, 1, 2, 1, 1, 1, 5, 1, 8]
def baseStart_3749075 : Nat := 118140960795 + 3749075 * 2 ^ 59
def prefixEnd_3749075 : Nat := 4983230072969 + 3 ^ 40 * 3749075 * 2
def baseEnd_3749075 : Nat := 1283384989836682973680549

theorem tailTrace_3749075 : CollatzResearch.WordTrace tailWord_3749075 prefixEnd_3749075 1283384989836682973680549 := by
  unfold tailWord_3749075
  simp only [CollatzResearch.WordTrace]
  refine ⟨136739998892749040878936679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91159999261832693919291119 136739998892749040878936679)
  ·
    refine ⟨205109998339123561318405019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136739998892749040878936679 205109998339123561318405019)
    ·
      refine ⟨307664997508685341977607529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205109998339123561318405019 307664997508685341977607529)
      ·
        refine ⟨230748748131514006483205647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307664997508685341977607529 230748748131514006483205647)
        ·
          refine ⟨346123122197271009724808471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230748748131514006483205647 346123122197271009724808471)
          ·
            refine ⟨519184683295906514587212707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346123122197271009724808471 519184683295906514587212707)
            ·
              refine ⟨778777024943859771880819061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 519184683295906514587212707 778777024943859771880819061)
              ·
                refine ⟨73010346088486853613826787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 778777024943859771880819061 73010346088486853613826787)
                ·
                  refine ⟨109515519132730280420740181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73010346088486853613826787 109515519132730280420740181)
                  ·
                    refine ⟨1283384989836682973680549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 109515519132730280420740181 1283384989836682973680549)
                    ·
                      rfl

theorem cell22_3749075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 8].length) (baseStart_3749075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3749075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3749075 prefixEnd_3749075 := by exact prefixLift 3749075
  have htrace : WordTrace (prefixWord ++ tailWord_3749075) baseStart_3749075 baseEnd_3749075 := by
    simpa [prefixWord, tailWord_3749075, baseEnd_3749075] using wordTrace_append hprefix tailTrace_3749075
  have hstable : (prefixWord ++ tailWord_3749075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749075).length < 2 ^ (prefixWord ++ tailWord_3749075).sum := by decide
  have hdescent : baseEnd_3749075 < baseStart_3749075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749124 : List Nat := [2, 3, 2, 2, 2, 1, 1, 4, 5]
def baseStart_3749124 : Nat := 118140960795 + 3749124 * 2 ^ 59
def prefixEnd_3749124 : Nat := 4983230072969 + 3 ^ 40 * 3749124 * 2
def baseEnd_3749124 : Nat := 427800587846021059735133

theorem tailTrace_3749124 : CollatzResearch.WordTrace tailWord_3749124 prefixEnd_3749124 427800587846021059735133 := by
  unfold tailWord_3749124
  simp only [CollatzResearch.WordTrace]
  refine ⟨68370893034785761123735213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91161190713047681498313617 68370893034785761123735213)
  ·
    refine ⟨25639084888044660421400705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68370893034785761123735213 25639084888044660421400705)
    ·
      refine ⟨19229313666033495316050529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25639084888044660421400705 19229313666033495316050529)
      ·
        refine ⟨14421985249525121487037897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19229313666033495316050529 14421985249525121487037897)
        ·
          refine ⟨10816488937143841115278423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14421985249525121487037897 10816488937143841115278423)
          ·
            refine ⟨16224733405715761672917635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10816488937143841115278423 16224733405715761672917635)
            ·
              refine ⟨24337100108573642509376453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16224733405715761672917635 24337100108573642509376453)
              ·
                refine ⟨4563206270357557970508085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24337100108573642509376453 4563206270357557970508085)
                ·
                  refine ⟨427800587846021059735133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4563206270357557970508085 427800587846021059735133)
                  ·
                    rfl

theorem cell22_3749124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 4, 5].length) (baseStart_3749124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3749124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3749124 prefixEnd_3749124 := by exact prefixLift 3749124
  have htrace : WordTrace (prefixWord ++ tailWord_3749124) baseStart_3749124 baseEnd_3749124 := by
    simpa [prefixWord, tailWord_3749124, baseEnd_3749124] using wordTrace_append hprefix tailTrace_3749124
  have hstable : (prefixWord ++ tailWord_3749124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749124).length < 2 ^ (prefixWord ++ tailWord_3749124).sum := by decide
  have hdescent : baseEnd_3749124 < baseStart_3749124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749128 : List Nat := [2, 1, 3, 2, 4, 1, 1, 4, 1, 3]
def baseStart_3749128 : Nat := 118140960795 + 3749128 * 2 ^ 59
def prefixEnd_3749128 : Nat := 4983230072969 + 3 ^ 40 * 3749128 * 2
def baseEnd_3749128 : Nat := 1283403132819808502105387

theorem tailTrace_3749128 : CollatzResearch.WordTrace tailWord_3749128 prefixEnd_3749128 1283403132819808502105387 := by
  unfold tailWord_3749128
  simp only [CollatzResearch.WordTrace]
  refine ⟨68370965980778515465308019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91161287974371353953744025 68370965980778515465308019)
  ·
    refine ⟨102556448971167773197962029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68370965980778515465308019 102556448971167773197962029)
    ·
      refine ⟨38458668364187914949235761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102556448971167773197962029 38458668364187914949235761)
      ·
        refine ⟨28844001273140936211926821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38458668364187914949235761 28844001273140936211926821)
        ·
          refine ⟨5408250238713925539736279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28844001273140936211926821 5408250238713925539736279)
          ·
            refine ⟨8112375358070888309604419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5408250238713925539736279 8112375358070888309604419)
            ·
              refine ⟨12168563037106332464406629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8112375358070888309604419 12168563037106332464406629)
              ·
                refine ⟨2281605569457437337076243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12168563037106332464406629 2281605569457437337076243)
                ·
                  refine ⟨3422408354186156005614365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2281605569457437337076243 3422408354186156005614365)
                  ·
                    refine ⟨1283403132819808502105387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3422408354186156005614365 1283403132819808502105387)
                    ·
                      rfl

theorem cell22_3749128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 4, 1, 3].length) (baseStart_3749128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3749128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3749128 prefixEnd_3749128 := by exact prefixLift 3749128
  have htrace : WordTrace (prefixWord ++ tailWord_3749128) baseStart_3749128 baseEnd_3749128 := by
    simpa [prefixWord, tailWord_3749128, baseEnd_3749128] using wordTrace_append hprefix tailTrace_3749128
  have hstable : (prefixWord ++ tailWord_3749128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749128).length < 2 ^ (prefixWord ++ tailWord_3749128).sum := by decide
  have hdescent : baseEnd_3749128 < baseStart_3749128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749137 : List Nat := [1, 2, 2, 1, 1, 4, 1, 1, 5, 4]
def baseStart_3749137 : Nat := 118140960795 + 3749137 * 2 ^ 59
def prefixEnd_3749137 : Nat := 4983230072969 + 3 ^ 40 * 3749137 * 2
def baseEnd_3749137 : Nat := 1283406213703735478630359

theorem tailTrace_3749137 : CollatzResearch.WordTrace tailWord_3749137 prefixEnd_3749137 1283406213703735478630359 := by
  unfold tailWord_3749137
  simp only [CollatzResearch.WordTrace]
  refine ⟨136742260218524425467693665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91161506812349616978462443 136742260218524425467693665)
  ·
    refine ⟨102556695163893319100770249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136742260218524425467693665 102556695163893319100770249)
    ·
      refine ⟨76917521372919989325577687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102556695163893319100770249 76917521372919989325577687)
      ·
        refine ⟨115376282059379983988366531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76917521372919989325577687 115376282059379983988366531)
        ·
          refine ⟨173064423089069975982549797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115376282059379983988366531 173064423089069975982549797)
          ·
            refine ⟨32449579329200620496728087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 173064423089069975982549797 32449579329200620496728087)
            ·
              refine ⟨48674368993800930745092131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32449579329200620496728087 48674368993800930745092131)
              ·
                refine ⟨73011553490701396117638197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48674368993800930745092131 73011553490701396117638197)
                ·
                  refine ⟨6844833139753255886028581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73011553490701396117638197 6844833139753255886028581)
                  ·
                    refine ⟨1283406213703735478630359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6844833139753255886028581 1283406213703735478630359)
                    ·
                      rfl

theorem cell22_3749137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 4].length) (baseStart_3749137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3749137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3749137 prefixEnd_3749137 := by exact prefixLift 3749137
  have htrace : WordTrace (prefixWord ++ tailWord_3749137) baseStart_3749137 baseEnd_3749137 := by
    simpa [prefixWord, tailWord_3749137, baseEnd_3749137] using wordTrace_append hprefix tailTrace_3749137
  have hstable : (prefixWord ++ tailWord_3749137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749137).length < 2 ^ (prefixWord ++ tailWord_3749137).sum := by decide
  have hdescent : baseEnd_3749137 < baseStart_3749137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749171 : List Nat := [1, 1, 1, 2, 5, 2, 4, 1, 1, 4]
def baseStart_3749171 : Nat := 118140960795 + 3749171 * 2 ^ 59
def prefixEnd_3749171 : Nat := 4983230072969 + 3 ^ 40 * 3749171 * 2
def baseEnd_3749171 : Nat := 1283417852598570723280255

theorem tailTrace_3749171 : CollatzResearch.WordTrace tailWord_3749171 prefixEnd_3749171 1283417852598570723280255 := by
  unfold tailWord_3749171
  simp only [CollatzResearch.WordTrace]
  refine ⟨136743500300401249274431367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91162333533600832849620911 136743500300401249274431367)
  ·
    refine ⟨205115250450601873911647051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136743500300401249274431367 205115250450601873911647051)
    ·
      refine ⟨307672875675902810867470577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205115250450601873911647051 307672875675902810867470577)
      ·
        refine ⟨230754656756927108150602933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307672875675902810867470577 230754656756927108150602933)
        ·
          refine ⟨21633249070961916389119025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 230754656756927108150602933 21633249070961916389119025)
          ·
            refine ⟨16224936803221437291839269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21633249070961916389119025 16224936803221437291839269)
            ·
              refine ⟨3042175650604019492219863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16224936803221437291839269 3042175650604019492219863)
              ·
                refine ⟨4563263475906029238329795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3042175650604019492219863 4563263475906029238329795)
                ·
                  refine ⟨6844895213859043857494693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4563263475906029238329795 6844895213859043857494693)
                  ·
                    refine ⟨1283417852598570723280255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6844895213859043857494693 1283417852598570723280255)
                    ·
                      rfl

theorem cell22_3749171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 4, 1, 1, 4].length) (baseStart_3749171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3749171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3749171 prefixEnd_3749171 := by exact prefixLift 3749171
  have htrace : WordTrace (prefixWord ++ tailWord_3749171) baseStart_3749171 baseEnd_3749171 := by
    simpa [prefixWord, tailWord_3749171, baseEnd_3749171] using wordTrace_append hprefix tailTrace_3749171
  have hstable : (prefixWord ++ tailWord_3749171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749171).length < 2 ^ (prefixWord ++ tailWord_3749171).sum := by decide
  have hdescent : baseEnd_3749171 < baseStart_3749171 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749184 : List Nat := [2, 1, 1, 2, 2, 1, 5, 1, 4, 3]
def baseStart_3749184 : Nat := 118140960795 + 3749184 * 2 ^ 59
def prefixEnd_3749184 : Nat := 4983230072969 + 3 ^ 40 * 3749184 * 2
def baseEnd_3749184 : Nat := 1283422302764243022705215

theorem tailTrace_3749184 : CollatzResearch.WordTrace tailWord_3749184 prefixEnd_3749184 1283422302764243022705215 := by
  unfold tailWord_3749184
  simp only [CollatzResearch.WordTrace]
  refine ⟨68371987224677076247327303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91162649632902768329769737 68371987224677076247327303)
  ·
    refine ⟨102557980837015614370990955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68371987224677076247327303 102557980837015614370990955)
    ·
      refine ⟨153836971255523421556486433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102557980837015614370990955 153836971255523421556486433)
      ·
        refine ⟨115377728441642566167364825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153836971255523421556486433 115377728441642566167364825)
        ·
          refine ⟨86533296331231924625523619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115377728441642566167364825 86533296331231924625523619)
          ·
            refine ⟨129799944496847886938285429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86533296331231924625523619 129799944496847886938285429)
            ·
              refine ⟨12168744796579489400464259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 129799944496847886938285429 12168744796579489400464259)
              ·
                refine ⟨18253117194869234100696389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12168744796579489400464259 18253117194869234100696389)
                ·
                  refine ⟨3422459474037981393880573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18253117194869234100696389 3422459474037981393880573)
                  ·
                    refine ⟨1283422302764243022705215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3422459474037981393880573 1283422302764243022705215)
                    ·
                      rfl

theorem cell22_3749184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 4, 3].length) (baseStart_3749184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3749184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3749184 prefixEnd_3749184 := by exact prefixLift 3749184
  have htrace : WordTrace (prefixWord ++ tailWord_3749184) baseStart_3749184 baseEnd_3749184 := by
    simpa [prefixWord, tailWord_3749184, baseEnd_3749184] using wordTrace_append hprefix tailTrace_3749184
  have hstable : (prefixWord ++ tailWord_3749184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749184).length < 2 ^ (prefixWord ++ tailWord_3749184).sum := by decide
  have hdescent : baseEnd_3749184 < baseStart_3749184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749259 : List Nat := [1, 1, 1, 1, 4, 3, 3, 3, 5]
def baseStart_3749259 : Nat := 118140960795 + 3749259 * 2 ^ 59
def prefixEnd_3749259 : Nat := 4983230072969 + 3 ^ 40 * 3749259 * 2
def baseEnd_3749259 : Nat := 427815992265655942359995

theorem tailTrace_3749259 : CollatzResearch.WordTrace tailWord_3749259 prefixEnd_3749259 427815992265655942359995 := by
  unfold tailWord_3749259
  simp only [CollatzResearch.WordTrace]
  refine ⟨136746709924082440303634831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91164473282721626869089887 136746709924082440303634831)
  ·
    refine ⟨205120064886123660455452247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136746709924082440303634831 205120064886123660455452247)
    ·
      refine ⟨307680097329185490683178371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205120064886123660455452247 307680097329185490683178371)
      ·
        refine ⟨461520145993778236024767557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307680097329185490683178371 461520145993778236024767557)
        ·
          refine ⟨86535027373833419254643917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 461520145993778236024767557 86535027373833419254643917)
          ·
            refine ⟨32450635265187532220491469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86535027373833419254643917 32450635265187532220491469)
            ·
              refine ⟨12168988224445324582684301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32450635265187532220491469 12168988224445324582684301)
              ·
                refine ⟨4563370584166996718506613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12168988224445324582684301 4563370584166996718506613)
                ·
                  refine ⟨427815992265655942359995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4563370584166996718506613 427815992265655942359995)
                  ·
                    rfl

theorem cell22_3749259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 3, 5].length) (baseStart_3749259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3749259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3749259 prefixEnd_3749259 := by exact prefixLift 3749259
  have htrace : WordTrace (prefixWord ++ tailWord_3749259) baseStart_3749259 baseEnd_3749259 := by
    simpa [prefixWord, tailWord_3749259, baseEnd_3749259] using wordTrace_append hprefix tailTrace_3749259
  have hstable : (prefixWord ++ tailWord_3749259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749259).length < 2 ^ (prefixWord ++ tailWord_3749259).sum := by decide
  have hdescent : baseEnd_3749259 < baseStart_3749259 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749293 : List Nat := [1, 5, 2, 2, 1, 2, 2, 2, 5]
def baseStart_3749293 : Nat := 118140960795 + 3749293 * 2 ^ 59
def prefixEnd_3749293 : Nat := 4983230072969 + 3 ^ 40 * 3749293 * 2
def baseEnd_3749293 : Nat := 427819871897267690576627

theorem tailTrace_3749293 : CollatzResearch.WordTrace tailWord_3749293 prefixEnd_3749293 427819871897267690576627 := by
  unfold tailWord_3749293
  simp only [CollatzResearch.WordTrace]
  refine ⟨136747950005959264110372533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91165300003972842740248355 136747950005959264110372533)
  ·
    refine ⟨12820120313058681010347425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 136747950005959264110372533 12820120313058681010347425)
    ·
      refine ⟨9615090234794010757760569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12820120313058681010347425 9615090234794010757760569)
      ·
        refine ⟨7211317676095508068320427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9615090234794010757760569 7211317676095508068320427)
        ·
          refine ⟨10816976514143262102480641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7211317676095508068320427 10816976514143262102480641)
          ·
            refine ⟨8112732385607446576860481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10816976514143262102480641 8112732385607446576860481)
            ·
              refine ⟨6084549289205584932645361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8112732385607446576860481 6084549289205584932645361)
              ·
                refine ⟨4563411966904188699484021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6084549289205584932645361 4563411966904188699484021)
                ·
                  refine ⟨427819871897267690576627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4563411966904188699484021 427819871897267690576627)
                  ·
                    rfl

theorem cell22_3749293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_3749293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3749293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3749293 prefixEnd_3749293 := by exact prefixLift 3749293
  have htrace : WordTrace (prefixWord ++ tailWord_3749293) baseStart_3749293 baseEnd_3749293 := by
    simpa [prefixWord, tailWord_3749293, baseEnd_3749293] using wordTrace_append hprefix tailTrace_3749293
  have hstable : (prefixWord ++ tailWord_3749293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749293).length < 2 ^ (prefixWord ++ tailWord_3749293).sum := by decide
  have hdescent : baseEnd_3749293 < baseStart_3749293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749314 : List Nat := [3, 5, 2, 1, 1, 1, 1, 2, 3, 3]
def baseStart_3749314 : Nat := 118140960795 + 3749314 * 2 ^ 59
def prefixEnd_3749314 : Nat := 4983230072969 + 3 ^ 40 * 3749314 * 2
def baseEnd_3749314 : Nat := 1283466804420966016954817

theorem tailTrace_3749314 : CollatzResearch.WordTrace tailWord_3749314 prefixEnd_3749314 1283466804420966016954817 := by
  unfold tailWord_3749314
  simp only [CollatzResearch.WordTrace]
  refine ⟨34187178984720796174221749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91165810625922123131257997 34187178984720796174221749)
  ·
    refine ⟨3205048029817574641333289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34187178984720796174221749 3205048029817574641333289)
    ·
      refine ⟨2403786022363180980999967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3205048029817574641333289 2403786022363180980999967)
      ·
        refine ⟨3605679033544771471499951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2403786022363180980999967 3605679033544771471499951)
        ·
          refine ⟨5408518550317157207249927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3605679033544771471499951 5408518550317157207249927)
          ·
            refine ⟨8112777825475735810874891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5408518550317157207249927 8112777825475735810874891)
            ·
              refine ⟨12169166738213603716312337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8112777825475735810874891 12169166738213603716312337)
              ·
                refine ⟨9126875053660202787234253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12169166738213603716312337 9126875053660202787234253)
                ·
                  refine ⟨3422578145122576045212845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9126875053660202787234253 3422578145122576045212845)
                  ·
                    refine ⟨1283466804420966016954817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3422578145122576045212845 1283466804420966016954817)
                    ·
                      rfl

theorem cell22_3749314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_3749314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3749314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3749314 prefixEnd_3749314 := by exact prefixLift 3749314
  have htrace : WordTrace (prefixWord ++ tailWord_3749314) baseStart_3749314 baseEnd_3749314 := by
    simpa [prefixWord, tailWord_3749314, baseEnd_3749314] using wordTrace_append hprefix tailTrace_3749314
  have hstable : (prefixWord ++ tailWord_3749314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749314).length < 2 ^ (prefixWord ++ tailWord_3749314).sum := by decide
  have hdescent : baseEnd_3749314 < baseStart_3749314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749338 : List Nat := [3, 1, 1, 2, 3, 3, 2, 3, 4]
def baseStart_3749338 : Nat := 118140960795 + 3749338 * 2 ^ 59
def prefixEnd_3749338 : Nat := 4983230072969 + 3 ^ 40 * 3749338 * 2
def baseEnd_3749338 : Nat := 427825006703812651451581

theorem tailTrace_3749338 : CollatzResearch.WordTrace tailWord_3749338 prefixEnd_3749338 427825006703812651451581 := by
  unfold tailWord_3749338
  simp only [CollatzResearch.WordTrace]
  refine ⟨34187397822699059198940167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91166394193864157863840445 34187397822699059198940167)
  ·
    refine ⟨51281096734048588798410251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34187397822699059198940167 51281096734048588798410251)
    ·
      refine ⟨76921645101072883197615377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51281096734048588798410251 76921645101072883197615377)
      ·
        refine ⟨57691233825804662398211533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76921645101072883197615377 57691233825804662398211533)
        ·
          refine ⟨21634212684676748399329325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57691233825804662398211533 21634212684676748399329325)
          ·
            refine ⟨8112829756753780649748497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21634212684676748399329325 8112829756753780649748497)
            ·
              refine ⟨6084622317565335487311373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8112829756753780649748497 6084622317565335487311373)
              ·
                refine ⟨2281733369087000807741765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6084622317565335487311373 2281733369087000807741765)
                ·
                  refine ⟨427825006703812651451581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2281733369087000807741765 427825006703812651451581)
                  ·
                    rfl

theorem cell22_3749338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 3, 4].length) (baseStart_3749338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3749338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3749338 prefixEnd_3749338 := by exact prefixLift 3749338
  have htrace : WordTrace (prefixWord ++ tailWord_3749338) baseStart_3749338 baseEnd_3749338 := by
    simpa [prefixWord, tailWord_3749338, baseEnd_3749338] using wordTrace_append hprefix tailTrace_3749338
  have hstable : (prefixWord ++ tailWord_3749338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749338).length < 2 ^ (prefixWord ++ tailWord_3749338).sum := by decide
  have hdescent : baseEnd_3749338 < baseStart_3749338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749383 : List Nat := [1, 1, 4, 3, 2, 3, 2, 6]
def baseStart_3749383 : Nat := 118140960795 + 3749383 * 2 ^ 59
def prefixEnd_3749383 : Nat := 4983230072969 + 3 ^ 40 * 3749383 * 2
def baseEnd_3749383 : Nat := 142610047170119204108845

theorem tailTrace_3749383 : CollatzResearch.WordTrace tailWord_3749383 prefixEnd_3749383 142610047170119204108845 := by
  unfold tailWord_3749383
  simp only [CollatzResearch.WordTrace]
  refine ⟨136751232575633209481148803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91167488383755472987432535 136751232575633209481148803)
  ·
    refine ⟨205126848863449814221723205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136751232575633209481148803 205126848863449814221723205)
    ·
      refine ⟨38461284161896840166573101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 205126848863449814221723205 38461284161896840166573101)
      ·
        refine ⟨14422981560711315062464913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38461284161896840166573101 14422981560711315062464913)
        ·
          refine ⟨10817236170533486296848685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14422981560711315062464913 10817236170533486296848685)
          ·
            refine ⟨4056463563950057361318257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10817236170533486296848685 4056463563950057361318257)
            ·
              refine ⟨3042347672962543020988693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4056463563950057361318257 3042347672962543020988693)
              ·
                refine ⟨142610047170119204108845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3042347672962543020988693 142610047170119204108845)
                ·
                  rfl

theorem cell22_3749383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 2, 6].length) (baseStart_3749383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3749383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3749383 prefixEnd_3749383 := by exact prefixLift 3749383
  have htrace : WordTrace (prefixWord ++ tailWord_3749383) baseStart_3749383 baseEnd_3749383 := by
    simpa [prefixWord, tailWord_3749383, baseEnd_3749383] using wordTrace_append hprefix tailTrace_3749383
  have hstable : (prefixWord ++ tailWord_3749383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749383).length < 2 ^ (prefixWord ++ tailWord_3749383).sum := by decide
  have hdescent : baseEnd_3749383 < baseStart_3749383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749389 : List Nat := [1, 7, 1, 1, 2, 2, 1, 3, 4]
def baseStart_3749389 : Nat := 118140960795 + 3749389 * 2 ^ 59
def prefixEnd_3749389 : Nat := 4983230072969 + 3 ^ 40 * 3749389 * 2
def baseEnd_3749389 : Nat := 427830826151230273776529

theorem tailTrace_3749389 : CollatzResearch.WordTrace tailWord_3749389 prefixEnd_3749389 427830826151230273776529 := by
  unfold tailWord_3749389
  simp only [CollatzResearch.WordTrace]
  refine ⟨136751451413611472505867221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91167634275740981670578147 136751451413611472505867221)
  ·
    refine ⟨3205112142506518886856263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 136751451413611472505867221 3205112142506518886856263)
    ·
      refine ⟨4807668213759778330284395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3205112142506518886856263 4807668213759778330284395)
      ·
        refine ⟨7211502320639667495426593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4807668213759778330284395 7211502320639667495426593)
        ·
          refine ⟨5408626740479750621569945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7211502320639667495426593 5408626740479750621569945)
          ·
            refine ⟨4056470055359812966177459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5408626740479750621569945 4056470055359812966177459)
            ·
              refine ⟨6084705083039719449266189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4056470055359812966177459 6084705083039719449266189)
              ·
                refine ⟨2281764406139894793474821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6084705083039719449266189 2281764406139894793474821)
                ·
                  refine ⟨427830826151230273776529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2281764406139894793474821 427830826151230273776529)
                  ·
                    rfl

theorem cell22_3749389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_3749389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3749389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3749389 prefixEnd_3749389 := by exact prefixLift 3749389
  have htrace : WordTrace (prefixWord ++ tailWord_3749389) baseStart_3749389 baseEnd_3749389 := by
    simpa [prefixWord, tailWord_3749389, baseEnd_3749389] using wordTrace_append hprefix tailTrace_3749389
  have hstable : (prefixWord ++ tailWord_3749389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749389).length < 2 ^ (prefixWord ++ tailWord_3749389).sum := by decide
  have hdescent : baseEnd_3749389 < baseStart_3749389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749406 : List Nat := [4, 3, 3, 1, 1, 1, 3, 2, 4]
def baseStart_3749406 : Nat := 118140960795 + 3749406 * 2 ^ 59
def prefixEnd_3749406 : Nat := 4983230072969 + 3 ^ 40 * 3749406 * 2
def baseEnd_3749406 : Nat := 427832765967036147884845

theorem tailTrace_3749406 : CollatzResearch.WordTrace tailWord_3749406 prefixEnd_3749406 427832765967036147884845 := by
  unfold tailWord_3749406
  simp only [CollatzResearch.WordTrace]
  refine ⟨17094008931818735551154509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91168047636366589606157381 17094008931818735551154509)
  ·
    refine ⟨6410253349432025831682941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17094008931818735551154509 6410253349432025831682941)
    ·
      refine ⟨2403845006037009686881103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6410253349432025831682941 2403845006037009686881103)
      ·
        refine ⟨3605767509055514530321655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2403845006037009686881103 3605767509055514530321655)
        ·
          refine ⟨5408651263583271795482483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3605767509055514530321655 5408651263583271795482483)
          ·
            refine ⟨8112976895374907693223725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5408651263583271795482483 8112976895374907693223725)
            ·
              refine ⟨3042366335765590384958897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8112976895374907693223725 3042366335765590384958897)
              ·
                refine ⟨2281774751824192788719173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3042366335765590384958897 2281774751824192788719173)
                ·
                  refine ⟨427832765967036147884845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2281774751824192788719173 427832765967036147884845)
                  ·
                    rfl

theorem cell22_3749406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_3749406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3749406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3749406 prefixEnd_3749406 := by exact prefixLift 3749406
  have htrace : WordTrace (prefixWord ++ tailWord_3749406) baseStart_3749406 baseEnd_3749406 := by
    simpa [prefixWord, tailWord_3749406, baseEnd_3749406] using wordTrace_append hprefix tailTrace_3749406
  have hstable : (prefixWord ++ tailWord_3749406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749406).length < 2 ^ (prefixWord ++ tailWord_3749406).sum := by decide
  have hdescent : baseEnd_3749406 < baseStart_3749406 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749424 : List Nat := [2, 1, 1, 1, 2, 3, 1, 1, 2, 8]
def baseStart_3749424 : Nat := 118140960795 + 3749424 * 2 ^ 59
def prefixEnd_3749424 : Nat := 4983230072969 + 3 ^ 40 * 3749424 * 2
def baseEnd_3749424 : Nat := 1283504459668962396704479

theorem tailTrace_3749424 : CollatzResearch.WordTrace tailWord_3749424 prefixEnd_3749424 1283504459668962396704479 := by
  unfold tailWord_3749424
  simp only [CollatzResearch.WordTrace]
  refine ⟨68376363984242336741695663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91168485312323115655594217 68376363984242336741695663)
  ·
    refine ⟨102564545976363505112543495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68376363984242336741695663 102564545976363505112543495)
    ·
      refine ⟨153846818964545257668815243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102564545976363505112543495 153846818964545257668815243)
      ·
        refine ⟨230770228446817886503222865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153846818964545257668815243 230770228446817886503222865)
        ·
          refine ⟨173077671335113414877417149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230770228446817886503222865 173077671335113414877417149)
          ·
            refine ⟨64904126750667530579031431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173077671335113414877417149 64904126750667530579031431)
            ·
              refine ⟨97356190126001295868547147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64904126750667530579031431 97356190126001295868547147)
              ·
                refine ⟨146034285189001943802820721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97356190126001295868547147 146034285189001943802820721)
                ·
                  refine ⟨109525713891751457852115541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146034285189001943802820721 109525713891751457852115541)
                  ·
                    refine ⟨1283504459668962396704479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 109525713891751457852115541 1283504459668962396704479)
                    ·
                      rfl

theorem cell22_3749424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 2, 8].length) (baseStart_3749424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3749424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3749424 prefixEnd_3749424 := by exact prefixLift 3749424
  have htrace : WordTrace (prefixWord ++ tailWord_3749424) baseStart_3749424 baseEnd_3749424 := by
    simpa [prefixWord, tailWord_3749424, baseEnd_3749424] using wordTrace_append hprefix tailTrace_3749424
  have hstable : (prefixWord ++ tailWord_3749424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749424).length < 2 ^ (prefixWord ++ tailWord_3749424).sum := by decide
  have hdescent : baseEnd_3749424 < baseStart_3749424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749473 : List Nat := [1, 2, 3, 1, 1, 3, 3, 4, 4]
def baseStart_3749473 : Nat := 118140960795 + 3749473 * 2 ^ 59
def prefixEnd_3749473 : Nat := 4983230072969 + 3 ^ 40 * 3749473 * 2
def baseEnd_3749473 : Nat := 427840411123447534076443

theorem tailTrace_3749473 : CollatzResearch.WordTrace tailWord_3749473 prefixEnd_3749473 427840411123447534076443 := by
  unfold tailWord_3749473
  simp only [CollatzResearch.WordTrace]
  refine ⟨136754515145307154851925073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91169676763538103234616715 136754515145307154851925073)
  ·
    refine ⟨102565886358980366138943805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136754515145307154851925073 102565886358980366138943805)
    ·
      refine ⟨38462207384617637302103927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102565886358980366138943805 38462207384617637302103927)
      ·
        refine ⟨57693311076926455953155891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38462207384617637302103927 57693311076926455953155891)
        ·
          refine ⟨86539966615389683929733837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57693311076926455953155891 86539966615389683929733837)
          ·
            refine ⟨32452487480771131473650189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86539966615389683929733837 32452487480771131473650189)
            ·
              refine ⟨12169682805289174302618821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32452487480771131473650189 12169682805289174302618821)
              ·
                refine ⟨2281815525991720181741029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12169682805289174302618821 2281815525991720181741029)
                ·
                  refine ⟨427840411123447534076443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2281815525991720181741029 427840411123447534076443)
                  ·
                    rfl

theorem cell22_3749473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 4, 4].length) (baseStart_3749473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3749473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3749473 prefixEnd_3749473 := by exact prefixLift 3749473
  have htrace : WordTrace (prefixWord ++ tailWord_3749473) baseStart_3749473 baseEnd_3749473 := by
    simpa [prefixWord, tailWord_3749473, baseEnd_3749473] using wordTrace_append hprefix tailTrace_3749473
  have hstable : (prefixWord ++ tailWord_3749473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749473).length < 2 ^ (prefixWord ++ tailWord_3749473).sum := by decide
  have hdescent : baseEnd_3749473 < baseStart_3749473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749488 : List Nat := [2, 1, 1, 1, 6, 2, 2, 1, 1, 5]
def baseStart_3749488 : Nat := 118140960795 + 3749488 * 2 ^ 59
def prefixEnd_3749488 : Nat := 4983230072969 + 3 ^ 40 * 3749488 * 2
def baseEnd_3749488 : Nat := 1283526368176887563104283

theorem tailTrace_3749488 : CollatzResearch.WordTrace tailWord_3749488 prefixEnd_3749488 1283526368176887563104283 := by
  unfold tailWord_3749488
  simp only [CollatzResearch.WordTrace]
  refine ⟨68377531120126406206860559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91170041493501874942480745 68377531120126406206860559)
  ·
    refine ⟨102566296680189609310290839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68377531120126406206860559 102566296680189609310290839)
    ·
      refine ⟨153849445020284413965436259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102566296680189609310290839 153849445020284413965436259)
      ·
        refine ⟨230774167530426620948154389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153849445020284413965436259 230774167530426620948154389)
        ·
          refine ⟨10817539102988747856944737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 230774167530426620948154389 10817539102988747856944737)
          ·
            refine ⟨8113154327241560892708553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10817539102988747856944737 8113154327241560892708553)
            ·
              refine ⟨6084865745431170669531415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8113154327241560892708553 6084865745431170669531415)
              ·
                refine ⟨9127298618146756004297123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6084865745431170669531415 9127298618146756004297123)
                ·
                  refine ⟨13690947927220134006445685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9127298618146756004297123 13690947927220134006445685)
                  ·
                    refine ⟨1283526368176887563104283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13690947927220134006445685 1283526368176887563104283)
                    ·
                      rfl

theorem cell22_3749488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 1, 1, 5].length) (baseStart_3749488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3749488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3749488 prefixEnd_3749488 := by exact prefixLift 3749488
  have htrace : WordTrace (prefixWord ++ tailWord_3749488) baseStart_3749488 baseEnd_3749488 := by
    simpa [prefixWord, tailWord_3749488, baseEnd_3749488] using wordTrace_append hprefix tailTrace_3749488
  have hstable : (prefixWord ++ tailWord_3749488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749488).length < 2 ^ (prefixWord ++ tailWord_3749488).sum := by decide
  have hdescent : baseEnd_3749488 < baseStart_3749488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749561 : List Nat := [1, 2, 1, 4, 1, 1, 2, 2, 1, 7]
def baseStart_3749561 : Nat := 118140960795 + 3749561 * 2 ^ 59
def prefixEnd_3749561 : Nat := 4983230072969 + 3 ^ 40 * 3749561 * 2
def baseEnd_3749561 : Nat := 1283551357568739706029059

theorem tailTrace_3749561 : CollatzResearch.WordTrace tailWord_3749561 prefixEnd_3749561 1283551357568739706029059 := by
  unfold tailWord_3749561
  simp only [CollatzResearch.WordTrace]
  refine ⟨136757724768988345881128537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91171816512658897254085691 136757724768988345881128537)
  ·
    refine ⟨102568293576741259410846403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136757724768988345881128537 102568293576741259410846403)
    ·
      refine ⟨153852440365111889116269605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102568293576741259410846403 153852440365111889116269605)
      ·
        refine ⟨28847332568458479209300551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153852440365111889116269605 28847332568458479209300551)
        ·
          refine ⟨43270998852687718813950827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28847332568458479209300551 43270998852687718813950827)
          ·
            refine ⟨64906498279031578220926241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43270998852687718813950827 64906498279031578220926241)
            ·
              refine ⟨48679873709273683665694681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64906498279031578220926241 48679873709273683665694681)
              ·
                refine ⟨36509905281955262749271011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48679873709273683665694681 36509905281955262749271011)
                ·
                  refine ⟨54764857922932894123906517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36509905281955262749271011 54764857922932894123906517)
                  ·
                    refine ⟨1283551357568739706029059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54764857922932894123906517 1283551357568739706029059)
                    ·
                      rfl

theorem cell22_3749561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 7].length) (baseStart_3749561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3749561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3749561 prefixEnd_3749561 := by exact prefixLift 3749561
  have htrace : WordTrace (prefixWord ++ tailWord_3749561) baseStart_3749561 baseEnd_3749561 := by
    simpa [prefixWord, tailWord_3749561, baseEnd_3749561] using wordTrace_append hprefix tailTrace_3749561
  have hstable : (prefixWord ++ tailWord_3749561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749561).length < 2 ^ (prefixWord ++ tailWord_3749561).sum := by decide
  have hdescent : baseEnd_3749561 < baseStart_3749561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749597 : List Nat := [1, 4, 3, 3, 1, 1, 1, 3, 5]
def baseStart_3749597 : Nat := 118140960795 + 3749597 * 2 ^ 59
def prefixEnd_3749597 : Nat := 4983230072969 + 3 ^ 40 * 3749597 * 2
def baseEnd_3749597 : Nat := 427854560368149204042983

theorem tailTrace_3749597 : CollatzResearch.WordTrace tailWord_3749597 prefixEnd_3749597 427854560368149204042983 := by
  unfold tailWord_3749597
  simp only [CollatzResearch.WordTrace]
  refine ⟨136759037796857924029439045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91172691864571949352959363 136759037796857924029439045)
  ·
    refine ⟨25642319586910860755519821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136759037796857924029439045 25642319586910860755519821)
    ·
      refine ⟨9615869845091572783319933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25642319586910860755519821 9615869845091572783319933)
      ·
        refine ⟨3605951191909339793744975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9615869845091572783319933 3605951191909339793744975)
        ·
          refine ⟨5408926787864009690617463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3605951191909339793744975 5408926787864009690617463)
          ·
            refine ⟨8113390181796014535926195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5408926787864009690617463 8113390181796014535926195)
            ·
              refine ⟨12170085272694021803889293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8113390181796014535926195 12170085272694021803889293)
              ·
                refine ⟨4563781977260258176458485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12170085272694021803889293 4563781977260258176458485)
                ·
                  refine ⟨427854560368149204042983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4563781977260258176458485 427854560368149204042983)
                  ·
                    rfl

theorem cell22_3749597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 3, 5].length) (baseStart_3749597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3749597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3749597 prefixEnd_3749597 := by exact prefixLift 3749597
  have htrace : WordTrace (prefixWord ++ tailWord_3749597) baseStart_3749597 baseEnd_3749597 := by
    simpa [prefixWord, tailWord_3749597, baseEnd_3749597] using wordTrace_append hprefix tailTrace_3749597
  have hstable : (prefixWord ++ tailWord_3749597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749597).length < 2 ^ (prefixWord ++ tailWord_3749597).sum := by decide
  have hdescent : baseEnd_3749597 < baseStart_3749597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749610 : List Nat := [3, 1, 3, 1, 1, 1, 5, 2, 1, 4]
def baseStart_3749610 : Nat := 118140960795 + 3749610 * 2 ^ 59
def prefixEnd_3749610 : Nat := 4983230072969 + 3 ^ 40 * 3749610 * 2
def baseEnd_3749610 : Nat := 1283568131270119911553909

theorem tailTrace_3749610 : CollatzResearch.WordTrace tailWord_3749610 prefixEnd_3749610 1283568131270119911553909 := by
  unfold tailWord_3749610
  simp only [CollatzResearch.WordTrace]
  refine ⟨34189877986452706812415571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91173007963873884833108189 34189877986452706812415571)
  ·
    refine ⟨51284816979679060218623357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34189877986452706812415571 51284816979679060218623357)
    ·
      refine ⟨19231806367379647581983759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51284816979679060218623357 19231806367379647581983759)
      ·
        refine ⟨28847709551069471372975639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19231806367379647581983759 28847709551069471372975639)
        ·
          refine ⟨43271564326604207059463459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28847709551069471372975639 43271564326604207059463459)
          ·
            refine ⟨64907346489906310589195189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43271564326604207059463459 64907346489906310589195189)
            ·
              refine ⟨6085063733428716617737049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64907346489906310589195189 6085063733428716617737049)
              ·
                refine ⟨4563797800071537463302787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6085063733428716617737049 4563797800071537463302787)
                ·
                  refine ⟨6845696700107306194954181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4563797800071537463302787 6845696700107306194954181)
                  ·
                    refine ⟨1283568131270119911553909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6845696700107306194954181 1283568131270119911553909)
                    ·
                      rfl

theorem cell22_3749610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_3749610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3749610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3749610 prefixEnd_3749610 := by exact prefixLift 3749610
  have htrace : WordTrace (prefixWord ++ tailWord_3749610) baseStart_3749610 baseEnd_3749610 := by
    simpa [prefixWord, tailWord_3749610, baseEnd_3749610] using wordTrace_append hprefix tailTrace_3749610
  have hstable : (prefixWord ++ tailWord_3749610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749610).length < 2 ^ (prefixWord ++ tailWord_3749610).sum := by decide
  have hdescent : baseEnd_3749610 < baseStart_3749610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749623 : List Nat := [1, 1, 3, 1, 1, 1, 4, 1, 6, 3]
def baseStart_3749623 : Nat := 118140960795 + 3749623 * 2 ^ 59
def prefixEnd_3749623 : Nat := 4983230072969 + 3 ^ 40 * 3749623 * 2
def baseEnd_3749623 : Nat := 1283572581435792210978869

theorem tailTrace_3749623 : CollatzResearch.WordTrace tailWord_3749623 prefixEnd_3749623 1283572581435792210978869 := by
  unfold tailWord_3749623
  simp only [CollatzResearch.WordTrace]
  refine ⟨136759986094763730469885523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91173324063175820313257015 136759986094763730469885523)
  ·
    refine ⟨205139979142145595704828285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136759986094763730469885523 205139979142145595704828285)
    ·
      refine ⟨76927492178304598389310607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205139979142145595704828285 76927492178304598389310607)
      ·
        refine ⟨115391238267456897583965911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76927492178304598389310607 115391238267456897583965911)
        ·
          refine ⟨173086857401185346375948867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115391238267456897583965911 173086857401185346375948867)
          ·
            refine ⟨259630286101778019563923301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173086857401185346375948867 259630286101778019563923301)
            ·
              refine ⟨48680678644083378668235619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 259630286101778019563923301 48680678644083378668235619)
              ·
                refine ⟨73021017966125068002353429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48680678644083378668235619 73021017966125068002353429)
                ·
                  refine ⟨3422860217162112562610317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 73021017966125068002353429 3422860217162112562610317)
                  ·
                    refine ⟨1283572581435792210978869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3422860217162112562610317 1283572581435792210978869)
                    ·
                      rfl

theorem cell22_3749623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 6, 3].length) (baseStart_3749623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3749623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3749623 prefixEnd_3749623 := by exact prefixLift 3749623
  have htrace : WordTrace (prefixWord ++ tailWord_3749623) baseStart_3749623 baseEnd_3749623 := by
    simpa [prefixWord, tailWord_3749623, baseEnd_3749623] using wordTrace_append hprefix tailTrace_3749623
  have hstable : (prefixWord ++ tailWord_3749623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749623).length < 2 ^ (prefixWord ++ tailWord_3749623).sum := by decide
  have hdescent : baseEnd_3749623 < baseStart_3749623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749642 : List Nat := [3, 1, 2, 2, 1, 3, 4, 2, 4]
def baseStart_3749642 : Nat := 118140960795 + 3749642 * 2 ^ 59
def prefixEnd_3749642 : Nat := 4983230072969 + 3 ^ 40 * 3749642 * 2
def baseEnd_3749642 : Nat := 427859695174694164917937

theorem tailTrace_3749642 : CollatzResearch.WordTrace tailWord_3749642 prefixEnd_3749642 427859695174694164917937 := by
  unfold tailWord_3749642
  simp only [CollatzResearch.WordTrace]
  refine ⟨34190169770423724178706795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91173786054463264476551453 34190169770423724178706795)
  ·
    refine ⟨51285254655635586268060193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34190169770423724178706795 51285254655635586268060193)
    ·
      refine ⟨38463940991726689701045145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51285254655635586268060193 38463940991726689701045145)
      ·
        refine ⟨28847955743795017275783859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38463940991726689701045145 28847955743795017275783859)
        ·
          refine ⟨43271933615692525913675789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28847955743795017275783859 43271933615692525913675789)
          ·
            refine ⟨16226975105884697217628421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43271933615692525913675789 16226975105884697217628421)
            ·
              refine ⟨3042557832353380728305329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16226975105884697217628421 3042557832353380728305329)
              ·
                refine ⟨2281918374265035546228997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3042557832353380728305329 2281918374265035546228997)
                ·
                  refine ⟨427859695174694164917937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2281918374265035546228997 427859695174694164917937)
                  ·
                    rfl

theorem cell22_3749642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 4, 2, 4].length) (baseStart_3749642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3749642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3749642 prefixEnd_3749642 := by exact prefixLift 3749642
  have htrace : WordTrace (prefixWord ++ tailWord_3749642) baseStart_3749642 baseEnd_3749642 := by
    simpa [prefixWord, tailWord_3749642, baseEnd_3749642] using wordTrace_append hprefix tailTrace_3749642
  have hstable : (prefixWord ++ tailWord_3749642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749642).length < 2 ^ (prefixWord ++ tailWord_3749642).sum := by decide
  have hdescent : baseEnd_3749642 < baseStart_3749642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749653 : List Nat := [1, 3, 2, 1, 2, 3, 3, 7]
def baseStart_3749653 : Nat := 118140960795 + 3749653 * 2 ^ 59
def prefixEnd_3749653 : Nat := 4983230072969 + 3 ^ 40 * 3749653 * 2
def baseEnd_3749653 : Nat := 142620316783209125858753

theorem tailTrace_3749653 : CollatzResearch.WordTrace tailWord_3749653 prefixEnd_3749653 142620316783209125858753 := by
  unfold tailWord_3749653
  simp only [CollatzResearch.WordTrace]
  refine ⟨136761080284655045593477613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91174053523103363728985075 136761080284655045593477613)
  ·
    refine ⟨51285405106745642097554105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136761080284655045593477613 51285405106745642097554105)
    ·
      refine ⟨38464053830059231573165579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51285405106745642097554105 38464053830059231573165579)
      ·
        refine ⟨57696080745088847359748369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38464053830059231573165579 57696080745088847359748369)
        ·
          refine ⟨43272060558816635519811277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57696080745088847359748369 43272060558816635519811277)
          ·
            refine ⟨16227022709556238319929229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43272060558816635519811277 16227022709556238319929229)
            ·
              refine ⟨6085133516083589369973461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16227022709556238319929229 6085133516083589369973461)
              ·
                refine ⟨142620316783209125858753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6085133516083589369973461 142620316783209125858753)
                ·
                  rfl

theorem cell22_3749653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 7].length) (baseStart_3749653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3749653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3749653 prefixEnd_3749653 := by exact prefixLift 3749653
  have htrace : WordTrace (prefixWord ++ tailWord_3749653) baseStart_3749653 baseEnd_3749653 := by
    simpa [prefixWord, tailWord_3749653, baseEnd_3749653] using wordTrace_append hprefix tailTrace_3749653
  have hstable : (prefixWord ++ tailWord_3749653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749653).length < 2 ^ (prefixWord ++ tailWord_3749653).sum := by decide
  have hdescent : baseEnd_3749653 < baseStart_3749653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749672 : List Nat := [2, 1, 5, 1, 1, 4, 1, 1, 2, 4]
def baseStart_3749672 : Nat := 118140960795 + 3749672 * 2 ^ 59
def prefixEnd_3749672 : Nat := 4983230072969 + 3 ^ 40 * 3749672 * 2
def baseEnd_3749672 : Nat := 1283589355137172416503719

theorem tailTrace_3749672 : CollatzResearch.WordTrace tailWord_3749672 prefixEnd_3749672 1283589355137172416503719 := by
  unfold tailWord_3749672
  simp only [CollatzResearch.WordTrace]
  refine ⟨68380886635793105919209635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91174515514390807892279513 68380886635793105919209635)
  ·
    refine ⟨102571329953689658878814453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68380886635793105919209635 102571329953689658878814453)
    ·
      refine ⟨9616062183158405519888855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102571329953689658878814453 9616062183158405519888855)
      ·
        refine ⟨14424093274737608279833283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9616062183158405519888855 14424093274737608279833283)
        ·
          refine ⟨21636139912106412419749925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14424093274737608279833283 21636139912106412419749925)
          ·
            refine ⟨4056776233519952328703111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21636139912106412419749925 4056776233519952328703111)
            ·
              refine ⟨6085164350279928493054667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4056776233519952328703111 6085164350279928493054667)
              ·
                refine ⟨9127746525419892739582001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6085164350279928493054667 9127746525419892739582001)
                ·
                  refine ⟨6845809894064919554686501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9127746525419892739582001 6845809894064919554686501)
                  ·
                    refine ⟨1283589355137172416503719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6845809894064919554686501 1283589355137172416503719)
                    ·
                      rfl

theorem cell22_3749672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_3749672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3749672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3749672 prefixEnd_3749672 := by exact prefixLift 3749672
  have htrace : WordTrace (prefixWord ++ tailWord_3749672) baseStart_3749672 baseEnd_3749672 := by
    simpa [prefixWord, tailWord_3749672, baseEnd_3749672] using wordTrace_append hprefix tailTrace_3749672
  have hstable : (prefixWord ++ tailWord_3749672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749672).length < 2 ^ (prefixWord ++ tailWord_3749672).sum := by decide
  have hdescent : baseEnd_3749672 < baseStart_3749672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749745 : List Nat := [1, 2, 2, 2, 1, 3, 1, 5, 1, 4]
def baseStart_3749745 : Nat := 118140960795 + 3749745 * 2 ^ 59
def prefixEnd_3749745 : Nat := 4983230072969 + 3 ^ 40 * 3749745 * 2
def baseEnd_3749745 : Nat := 1283614344529024559428495

theorem tailTrace_3749745 : CollatzResearch.WordTrace tailWord_3749745 prefixEnd_3749745 1283614344529024559428495 := by
  unfold tailWord_3749745
  simp only [CollatzResearch.WordTrace]
  refine ⟨136764435800321745305826689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91176290533547830203884459 136764435800321745305826689)
  ·
    refine ⟨102573326850241308979370017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136764435800321745305826689 102573326850241308979370017)
    ·
      refine ⟨76929995137680981734527513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102573326850241308979370017 76929995137680981734527513)
      ·
        refine ⟨57697496353260736300895635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76929995137680981734527513 57697496353260736300895635)
        ·
          refine ⟨86546244529891104451343453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57697496353260736300895635 86546244529891104451343453)
          ·
            refine ⟨32454841698709164169253795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86546244529891104451343453 32454841698709164169253795)
            ·
              refine ⟨48682262548063746253880693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32454841698709164169253795 48682262548063746253880693)
              ·
                refine ⟨4563962113880976211301315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48682262548063746253880693 4563962113880976211301315)
                ·
                  refine ⟨6845943170821464316951973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4563962113880976211301315 6845943170821464316951973)
                  ·
                    refine ⟨1283614344529024559428495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6845943170821464316951973 1283614344529024559428495)
                    ·
                      rfl

theorem cell22_3749745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 5, 1, 4].length) (baseStart_3749745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3749745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3749745 prefixEnd_3749745 := by exact prefixLift 3749745
  have htrace : WordTrace (prefixWord ++ tailWord_3749745) baseStart_3749745 baseEnd_3749745 := by
    simpa [prefixWord, tailWord_3749745, baseEnd_3749745] using wordTrace_append hprefix tailTrace_3749745
  have hstable : (prefixWord ++ tailWord_3749745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749745).length < 2 ^ (prefixWord ++ tailWord_3749745).sum := by decide
  have hdescent : baseEnd_3749745 < baseStart_3749745 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749809 : List Nat := [1, 2, 2, 4, 2, 2, 2, 2, 2, 3]
def baseStart_3749809 : Nat := 118140960795 + 3749809 * 2 ^ 59
def prefixEnd_3749809 : Nat := 4983230072969 + 3 ^ 40 * 3749809 * 2
def baseEnd_3749809 : Nat := 1283636253036949725828299

theorem tailTrace_3749809 : CollatzResearch.WordTrace tailWord_3749809 prefixEnd_3749809 1283636253036949725828299 := by
  unfold tailWord_3749809
  simp only [CollatzResearch.WordTrace]
  refine ⟨136766770072089884236156481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91177846714726589490770987 136766770072089884236156481)
  ·
    refine ⟨102575077554067413177117361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136766770072089884236156481 102575077554067413177117361)
    ·
      refine ⟨76931308165550559882838021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102575077554067413177117361 76931308165550559882838021)
      ·
        refine ⟨14424620281040729978032129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76931308165550559882838021 14424620281040729978032129)
        ·
          refine ⟨10818465210780547483524097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14424620281040729978032129 10818465210780547483524097)
          ·
            refine ⟨8113848908085410612643073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10818465210780547483524097 8113848908085410612643073)
            ·
              refine ⟨6085386681064057959482305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8113848908085410612643073 6085386681064057959482305)
              ·
                refine ⟨4564040010798043469611729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6085386681064057959482305 4564040010798043469611729)
                ·
                  refine ⟨3423030008098532602208797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4564040010798043469611729 3423030008098532602208797)
                  ·
                    refine ⟨1283636253036949725828299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3423030008098532602208797 1283636253036949725828299)
                    ·
                      rfl

theorem cell22_3749809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 2, 2, 3].length) (baseStart_3749809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3749809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3749809 prefixEnd_3749809 := by exact prefixLift 3749809
  have htrace : WordTrace (prefixWord ++ tailWord_3749809) baseStart_3749809 baseEnd_3749809 := by
    simpa [prefixWord, tailWord_3749809, baseEnd_3749809] using wordTrace_append hprefix tailTrace_3749809
  have hstable : (prefixWord ++ tailWord_3749809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749809).length < 2 ^ (prefixWord ++ tailWord_3749809).sum := by decide
  have hdescent : baseEnd_3749809 < baseStart_3749809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749822 : List Nat := [4, 2, 1, 1, 1, 5, 1, 7]
def baseStart_3749822 : Nat := 118140960795 + 3749822 * 2 ^ 59
def prefixEnd_3749822 : Nat := 4983230072969 + 3 ^ 40 * 3749822 * 2
def baseEnd_3749822 : Nat := 142626744800291336139251

theorem tailTrace_3749822 : CollatzResearch.WordTrace tailWord_3749822 prefixEnd_3749822 142626744800291336139251 := by
  unfold tailWord_3749822
  simp only [CollatzResearch.WordTrace]
  refine ⟨17095905527630348432047465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91178162814028524970919813 17095905527630348432047465)
  ·
    refine ⟨12821929145722761324035599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17095905527630348432047465 12821929145722761324035599)
    ·
      refine ⟨19232893718584141986053399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12821929145722761324035599 19232893718584141986053399)
      ·
        refine ⟨28849340577876212979080099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19232893718584141986053399 28849340577876212979080099)
        ·
          refine ⟨43274010866814319468620149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28849340577876212979080099 43274010866814319468620149)
          ·
            refine ⟨4056938518763842450183139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43274010866814319468620149 4056938518763842450183139)
            ·
              refine ⟨6085407778145763675274709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4056938518763842450183139 6085407778145763675274709)
              ·
                refine ⟨142626744800291336139251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6085407778145763675274709 142626744800291336139251)
                ·
                  rfl

theorem cell22_3749822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 7].length) (baseStart_3749822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3749822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3749822 prefixEnd_3749822 := by exact prefixLift 3749822
  have htrace : WordTrace (prefixWord ++ tailWord_3749822) baseStart_3749822 baseEnd_3749822 := by
    simpa [prefixWord, tailWord_3749822, baseEnd_3749822] using wordTrace_append hprefix tailTrace_3749822
  have hstable : (prefixWord ++ tailWord_3749822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749822).length < 2 ^ (prefixWord ++ tailWord_3749822).sum := by decide
  have hdescent : baseEnd_3749822 < baseStart_3749822 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749880 : List Nat := [2, 1, 2, 1, 1, 3, 2, 1, 5, 4]
def baseStart_3749880 : Nat := 118140960795 + 3749880 * 2 ^ 59
def prefixEnd_3749880 : Nat := 4983230072969 + 3 ^ 40 * 3749880 * 2
def baseEnd_3749880 : Nat := 1283660557787929207303081

theorem tailTrace_3749880 : CollatzResearch.WordTrace tailWord_3749880 prefixEnd_3749880 1283660557787929207303081 := by
  unfold tailWord_3749880
  simp only [CollatzResearch.WordTrace]
  refine ⟨68384679827416331680995547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91179573103221775574660729 68384679827416331680995547)
  ·
    refine ⟨102577019741124497521493321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68384679827416331680995547 102577019741124497521493321)
    ·
      refine ⟨76932764805843373141119991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102577019741124497521493321 76932764805843373141119991)
      ·
        refine ⟨115399147208765059711679987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76932764805843373141119991 115399147208765059711679987)
        ·
          refine ⟨173098720813147589567519981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115399147208765059711679987 173098720813147589567519981)
          ·
            refine ⟨64912020304930346087819993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173098720813147589567519981 64912020304930346087819993)
            ·
              refine ⟨48684015228697759565864995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64912020304930346087819993 48684015228697759565864995)
              ·
                refine ⟨73026022843046639348797493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48684015228697759565864995 73026022843046639348797493)
                ·
                  refine ⟨6846189641535622438949765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73026022843046639348797493 6846189641535622438949765)
                  ·
                    refine ⟨1283660557787929207303081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6846189641535622438949765 1283660557787929207303081)
                    ·
                      rfl

theorem cell22_3749880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 5, 4].length) (baseStart_3749880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3749880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3749880 prefixEnd_3749880 := by exact prefixLift 3749880
  have htrace : WordTrace (prefixWord ++ tailWord_3749880) baseStart_3749880 baseEnd_3749880 := by
    simpa [prefixWord, tailWord_3749880, baseEnd_3749880] using wordTrace_append hprefix tailTrace_3749880
  have hstable : (prefixWord ++ tailWord_3749880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749880).length < 2 ^ (prefixWord ++ tailWord_3749880).sum := by decide
  have hdescent : baseEnd_3749880 < baseStart_3749880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749974 : List Nat := [5, 2, 2, 1, 1, 11]
def baseStart_3749974 : Nat := 118140960795 + 3749974 * 2 ^ 59
def prefixEnd_3749974 : Nat := 4983230072969 + 3 ^ 40 * 3749974 * 2
def baseEnd_3749974 : Nat := 15848058468011657968553

theorem tailTrace_3749974 : CollatzResearch.WordTrace tailWord_3749974 prefixEnd_3749974 15848058468011657968553 := by
  unfold tailWord_3749974
  simp only [CollatzResearch.WordTrace]
  refine ⟨8548299257280757338494561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91181858744328078277275317 8548299257280757338494561)
  ·
    refine ⟨6411224442960568003870921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8548299257280757338494561 6411224442960568003870921)
    ·
      refine ⟨4808418332220426002903191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6411224442960568003870921 4808418332220426002903191)
      ·
        refine ⟨7212627498330639004354787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4808418332220426002903191 7212627498330639004354787)
        ·
          refine ⟨10818941247495958506532181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7212627498330639004354787 10818941247495958506532181)
          ·
            refine ⟨15848058468011657968553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10818941247495958506532181 15848058468011657968553)
            ·
              rfl

theorem cell22_3749974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 11].length) (baseStart_3749974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3749974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3749974 prefixEnd_3749974 := by exact prefixLift 3749974
  have htrace : WordTrace (prefixWord ++ tailWord_3749974) baseStart_3749974 baseEnd_3749974 := by
    simpa [prefixWord, tailWord_3749974, baseEnd_3749974] using wordTrace_append hprefix tailTrace_3749974
  have hstable : (prefixWord ++ tailWord_3749974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749974).length < 2 ^ (prefixWord ++ tailWord_3749974).sum := by decide
  have hdescent : baseEnd_3749974 < baseStart_3749974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750006 : List Nat := [5, 1, 1, 2, 1, 3, 1, 2, 3, 3]
def baseStart_3750006 : Nat := 118140960795 + 3750006 * 2 ^ 59
def prefixEnd_3750006 : Nat := 4983230072969 + 3 ^ 40 * 3750006 * 2
def baseEnd_3750006 : Nat := 1283703690162906878652695

theorem tailTrace_3750006 : CollatzResearch.WordTrace tailWord_3750006 prefixEnd_3750006 1283703690162906878652695 := by
  unfold tailWord_3750006
  simp only [CollatzResearch.WordTrace]
  refine ⟨8548372203273511680067367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91182636834917457920718581 8548372203273511680067367)
  ·
    refine ⟨12822558304910267520101051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8548372203273511680067367 12822558304910267520101051)
    ·
      refine ⟨19233837457365401280151577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12822558304910267520101051 19233837457365401280151577)
      ·
        refine ⟨14425378093024050960113683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19233837457365401280151577 14425378093024050960113683)
        ·
          refine ⟨21638067139536076440170525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14425378093024050960113683 21638067139536076440170525)
          ·
            refine ⟨8114275177326028665063947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21638067139536076440170525 8114275177326028665063947)
            ·
              refine ⟨12171412765989042997595921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8114275177326028665063947 12171412765989042997595921)
              ·
                refine ⟨9128559574491782248196941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12171412765989042997595921 9128559574491782248196941)
                ·
                  refine ⟨3423209840434418343073853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9128559574491782248196941 3423209840434418343073853)
                  ·
                    refine ⟨1283703690162906878652695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3423209840434418343073853 1283703690162906878652695)
                    ·
                      rfl

theorem cell22_3750006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 2, 3, 3].length) (baseStart_3750006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3750006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3750006 prefixEnd_3750006 := by exact prefixLift 3750006
  have htrace : WordTrace (prefixWord ++ tailWord_3750006) baseStart_3750006 baseEnd_3750006 := by
    simpa [prefixWord, tailWord_3750006, baseEnd_3750006] using wordTrace_append hprefix tailTrace_3750006
  have hstable : (prefixWord ++ tailWord_3750006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750006).length < 2 ^ (prefixWord ++ tailWord_3750006).sum := by decide
  have hdescent : baseEnd_3750006 < baseStart_3750006 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750036 : List Nat := [2, 4, 2, 3, 1, 1, 1, 1, 7]
def baseStart_3750036 : Nat := 118140960795 + 3750036 * 2 ^ 59
def prefixEnd_3750036 : Nat := 4983230072969 + 3 ^ 40 * 3750036 * 2
def baseEnd_3750036 : Nat := 427904653258665600134201

theorem tailTrace_3750036 : CollatzResearch.WordTrace tailWord_3750036 prefixEnd_3750036 427904653258665600134201 := by
  unfold tailWord_3750036
  simp only [CollatzResearch.WordTrace]
  refine ⟨68387524721133751002334981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91183366294845001336446641 68387524721133751002334981)
  ·
    refine ⟨12822660885212578312937809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68387524721133751002334981 12822660885212578312937809)
    ·
      refine ⟨9616995663909433734703357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12822660885212578312937809 9616995663909433734703357)
      ·
        refine ⟨3606373373966037650513759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9616995663909433734703357 3606373373966037650513759)
        ·
          refine ⟨5409560060949056475770639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3606373373966037650513759 5409560060949056475770639)
          ·
            refine ⟨8114340091423584713655959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5409560060949056475770639 8114340091423584713655959)
            ·
              refine ⟨12171510137135377070483939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8114340091423584713655959 12171510137135377070483939)
              ·
                refine ⟨18257265205703065605725909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12171510137135377070483939 18257265205703065605725909)
                ·
                  refine ⟨427904653258665600134201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18257265205703065605725909 427904653258665600134201)
                  ·
                    rfl

theorem cell22_3750036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 7].length) (baseStart_3750036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3750036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3750036 prefixEnd_3750036 := by exact prefixLift 3750036
  have htrace : WordTrace (prefixWord ++ tailWord_3750036) baseStart_3750036 baseEnd_3750036 := by
    simpa [prefixWord, tailWord_3750036, baseEnd_3750036] using wordTrace_append hprefix tailTrace_3750036
  have hstable : (prefixWord ++ tailWord_3750036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750036).length < 2 ^ (prefixWord ++ tailWord_3750036).sum := by decide
  have hdescent : baseEnd_3750036 < baseStart_3750036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750094 : List Nat := [4, 1, 1, 1, 4, 1, 1, 1, 4, 4]
def baseStart_3750094 : Nat := 118140960795 + 3750094 * 2 ^ 59
def prefixEnd_3750094 : Nat := 4983230072969 + 3 ^ 40 * 3750094 * 2
def baseEnd_3750094 : Nat := 1283733814361303982452425

theorem tailTrace_3750094 : CollatzResearch.WordTrace tailWord_3750094 prefixEnd_3750094 1283733814361303982452425 := by
  unfold tailWord_3750094
  simp only [CollatzResearch.WordTrace]
  refine ⟨17097145609507172238785167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91184776584038251940187557 17097145609507172238785167)
  ·
    refine ⟨25645718414260758358177751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17097145609507172238785167 25645718414260758358177751)
    ·
      refine ⟨38468577621391137537266627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25645718414260758358177751 38468577621391137537266627)
      ·
        refine ⟨57702866432086706305899941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38468577621391137537266627 57702866432086706305899941)
        ·
          refine ⟨10819287456016257432356239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57702866432086706305899941 10819287456016257432356239)
          ·
            refine ⟨16228931184024386148534359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10819287456016257432356239 16228931184024386148534359)
            ·
              refine ⟨24343396776036579222801539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16228931184024386148534359 24343396776036579222801539)
              ·
                refine ⟨36515095164054868834202309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24343396776036579222801539 36515095164054868834202309)
                ·
                  refine ⟨6846580343260287906412933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36515095164054868834202309 6846580343260287906412933)
                  ·
                    refine ⟨1283733814361303982452425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6846580343260287906412933 1283733814361303982452425)
                    ·
                      rfl

theorem cell22_3750094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 4, 4].length) (baseStart_3750094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3750094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3750094 prefixEnd_3750094 := by exact prefixLift 3750094
  have htrace : WordTrace (prefixWord ++ tailWord_3750094) baseStart_3750094 baseEnd_3750094 := by
    simpa [prefixWord, tailWord_3750094, baseEnd_3750094] using wordTrace_append hprefix tailTrace_3750094
  have hstable : (prefixWord ++ tailWord_3750094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750094).length < 2 ^ (prefixWord ++ tailWord_3750094).sum := by decide
  have hdescent : baseEnd_3750094 < baseStart_3750094 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750098 : List Nat := [3, 2, 2, 2, 1, 3, 3, 2, 4]
def baseStart_3750098 : Nat := 118140960795 + 3750098 * 2 ^ 59
def prefixEnd_3750098 : Nat := 4983230072969 + 3 ^ 40 * 3750098 * 2
def baseEnd_3750098 : Nat := 427911727881016435117471

theorem tailTrace_3750098 : CollatzResearch.WordTrace tailWord_3750098 prefixEnd_3750098 427911727881016435117471 := by
  unfold tailWord_3750098
  simp only [CollatzResearch.WordTrace]
  refine ⟨34194327692010721648356737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91184873845361924395617965 34194327692010721648356737)
  ·
    refine ⟨25645745769008041236267553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34194327692010721648356737 25645745769008041236267553)
    ·
      refine ⟨19234309326756030927200665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25645745769008041236267553 19234309326756030927200665)
      ·
        refine ⟨14425731995067023195400499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19234309326756030927200665 14425731995067023195400499)
        ·
          refine ⟨21638597992600534793100749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14425731995067023195400499 21638597992600534793100749)
          ·
            refine ⟨8114474247225200547412781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21638597992600534793100749 8114474247225200547412781)
            ·
              refine ⟨3042927842709450205279793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8114474247225200547412781 3042927842709450205279793)
              ·
                refine ⟨2282195882032087653959845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3042927842709450205279793 2282195882032087653959845)
                ·
                  refine ⟨427911727881016435117471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2282195882032087653959845 427911727881016435117471)
                  ·
                    rfl

theorem cell22_3750098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 3, 2, 4].length) (baseStart_3750098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3750098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3750098 prefixEnd_3750098 := by exact prefixLift 3750098
  have htrace : WordTrace (prefixWord ++ tailWord_3750098) baseStart_3750098 baseEnd_3750098 := by
    simpa [prefixWord, tailWord_3750098, baseEnd_3750098] using wordTrace_append hprefix tailTrace_3750098
  have hstable : (prefixWord ++ tailWord_3750098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750098).length < 2 ^ (prefixWord ++ tailWord_3750098).sum := by decide
  have hdescent : baseEnd_3750098 < baseStart_3750098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750109 : List Nat := [1, 4, 3, 2, 1, 1, 1, 9]
def baseStart_3750109 : Nat := 118140960795 + 3750109 * 2 ^ 59
def prefixEnd_3750109 : Nat := 4983230072969 + 3 ^ 40 * 3750109 * 2
def baseEnd_3750109 : Nat := 142637661018649882591931

theorem tailTrace_3750109 : CollatzResearch.WordTrace tailWord_3750109 prefixEnd_3750109 142637661018649882591931 := by
  unfold tailWord_3750109
  simp only [CollatzResearch.WordTrace]
  refine ⟨136777711971003035472077381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91185141314002023648051587 136777711971003035472077381)
  ·
    refine ⟨25645820994563069151014509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136777711971003035472077381 25645820994563069151014509)
    ·
      refine ⟨9617182872961150931630441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25645820994563069151014509 9617182872961150931630441)
      ·
        refine ⟨7212887154720863198722831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9617182872961150931630441 7212887154720863198722831)
        ·
          refine ⟨10819330732081294798084247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7212887154720863198722831 10819330732081294798084247)
          ·
            refine ⟨16228996098121942197126371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10819330732081294798084247 16228996098121942197126371)
            ·
              refine ⟨24343494147182913295689557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16228996098121942197126371 24343494147182913295689557)
              ·
                refine ⟨142637661018649882591931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24343494147182913295689557 142637661018649882591931)
                ·
                  rfl

theorem cell22_3750109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 9].length) (baseStart_3750109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3750109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3750109 prefixEnd_3750109 := by exact prefixLift 3750109
  have htrace : WordTrace (prefixWord ++ tailWord_3750109) baseStart_3750109 baseEnd_3750109 := by
    simpa [prefixWord, tailWord_3750109, baseEnd_3750109] using wordTrace_append hprefix tailTrace_3750109
  have hstable : (prefixWord ++ tailWord_3750109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750109).length < 2 ^ (prefixWord ++ tailWord_3750109).sum := by decide
  have hdescent : baseEnd_3750109 < baseStart_3750109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750124 : List Nat := [2, 2, 1, 1, 2, 3, 2, 1, 5, 3]
def baseStart_3750124 : Nat := 118140960795 + 3750124 * 2 ^ 59
def prefixEnd_3750124 : Nat := 4983230072969 + 3 ^ 40 * 3750124 * 2
def baseEnd_3750124 : Nat := 1283744083974393904202333

theorem tailTrace_3750124 : CollatzResearch.WordTrace tailWord_3750124 prefixEnd_3750124 1283744083974393904202333 := by
  unfold tailWord_3750124
  simp only [CollatzResearch.WordTrace]
  refine ⟨68389129532974346516936713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91185506043965795355915617 68389129532974346516936713)
  ·
    refine ⟨51291847149730759887702535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68389129532974346516936713 51291847149730759887702535)
    ·
      refine ⟨76937770724596139831553803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51291847149730759887702535 76937770724596139831553803)
      ·
        refine ⟨115406656086894209747330705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76937770724596139831553803 115406656086894209747330705)
        ·
          refine ⟨86554992065170657310498029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115406656086894209747330705 86554992065170657310498029)
          ·
            refine ⟨32458122024438996491436761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86554992065170657310498029 32458122024438996491436761)
            ·
              refine ⟨24343591518329247368577571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32458122024438996491436761 24343591518329247368577571)
              ·
                refine ⟨36515387277493871052866357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24343591518329247368577571 36515387277493871052866357)
                ·
                  refine ⟨3423317557265050411206221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36515387277493871052866357 3423317557265050411206221)
                  ·
                    refine ⟨1283744083974393904202333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3423317557265050411206221 1283744083974393904202333)
                    ·
                      rfl

theorem cell22_3750124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 3].length) (baseStart_3750124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3750124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3750124 prefixEnd_3750124 := by exact prefixLift 3750124
  have htrace : WordTrace (prefixWord ++ tailWord_3750124) baseStart_3750124 baseEnd_3750124 := by
    simpa [prefixWord, tailWord_3750124, baseEnd_3750124] using wordTrace_append hprefix tailTrace_3750124
  have hstable : (prefixWord ++ tailWord_3750124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750124).length < 2 ^ (prefixWord ++ tailWord_3750124).sum := by decide
  have hdescent : baseEnd_3750124 < baseStart_3750124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750137 : List Nat := [1, 2, 1, 3, 1, 1, 2, 4, 7]
def baseStart_3750137 : Nat := 118140960795 + 3750137 * 2 ^ 59
def prefixEnd_3750137 : Nat := 4983230072969 + 3 ^ 40 * 3750137 * 2
def baseEnd_3750137 : Nat := 427916178046688734542431

theorem tailTrace_3750137 : CollatzResearch.WordTrace tailWord_3750137 prefixEnd_3750137 427916178046688734542431 := by
  unfold tailWord_3750137
  simp only [CollatzResearch.WordTrace]
  refine ⟨136778733214901596254096665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91185822143267730836064443 136778733214901596254096665)
  ·
    refine ⟨102584049911176197190572499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136778733214901596254096665 102584049911176197190572499)
    ·
      refine ⟨153876074866764295785858749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102584049911176197190572499 153876074866764295785858749)
      ·
        refine ⟨57703528075036610919697031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153876074866764295785858749 57703528075036610919697031)
        ·
          refine ⟨86555292112554916379545547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57703528075036610919697031 86555292112554916379545547)
          ·
            refine ⟨129832938168832374569318321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86555292112554916379545547 129832938168832374569318321)
            ·
              refine ⟨97374703626624280926988741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129832938168832374569318321 97374703626624280926988741)
              ·
                refine ⟨18257756929992052673810389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97374703626624280926988741 18257756929992052673810389)
                ·
                  refine ⟨427916178046688734542431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18257756929992052673810389 427916178046688734542431)
                  ·
                    rfl

theorem cell22_3750137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 7].length) (baseStart_3750137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3750137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3750137 prefixEnd_3750137 := by exact prefixLift 3750137
  have htrace : WordTrace (prefixWord ++ tailWord_3750137) baseStart_3750137 baseEnd_3750137 := by
    simpa [prefixWord, tailWord_3750137, baseEnd_3750137] using wordTrace_append hprefix tailTrace_3750137
  have hstable : (prefixWord ++ tailWord_3750137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750137).length < 2 ^ (prefixWord ++ tailWord_3750137).sum := by decide
  have hdescent : baseEnd_3750137 < baseStart_3750137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750154 : List Nat := [3, 1, 2, 2, 1, 1, 3, 4, 5]
def baseStart_3750154 : Nat := 118140960795 + 3750154 * 2 ^ 59
def prefixEnd_3750154 : Nat := 4983230072969 + 3 ^ 40 * 3750154 * 2
def baseEnd_3750154 : Nat := 427918117862494608650747

theorem tailTrace_3750154 : CollatzResearch.WordTrace tailWord_3750154 prefixEnd_3750154 427918117862494608650747 := by
  unfold tailWord_3750154
  simp only [CollatzResearch.WordTrace]
  refine ⟨34194838313960002039366379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91186235503893338771643677 34194838313960002039366379)
  ·
    refine ⟨51292257470940003059049569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34194838313960002039366379 51292257470940003059049569)
    ·
      refine ⟨38469193103205002294287177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51292257470940003059049569 38469193103205002294287177)
      ·
        refine ⟨28851894827403751720715383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38469193103205002294287177 28851894827403751720715383)
        ·
          refine ⟨43277842241105627581073075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28851894827403751720715383 43277842241105627581073075)
          ·
            refine ⟨64916763361658441371609613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43277842241105627581073075 64916763361658441371609613)
            ·
              refine ⟨24343786260621915514353605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64916763361658441371609613 24343786260621915514353605)
              ·
                refine ⟨4564459923866609158941301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24343786260621915514353605 4564459923866609158941301)
                ·
                  refine ⟨427918117862494608650747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4564459923866609158941301 427918117862494608650747)
                  ·
                    rfl

theorem cell22_3750154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 4, 5].length) (baseStart_3750154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3750154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3750154 prefixEnd_3750154 := by exact prefixLift 3750154
  have htrace : WordTrace (prefixWord ++ tailWord_3750154) baseStart_3750154 baseEnd_3750154 := by
    simpa [prefixWord, tailWord_3750154, baseEnd_3750154] using wordTrace_append hprefix tailTrace_3750154
  have hstable : (prefixWord ++ tailWord_3750154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750154).length < 2 ^ (prefixWord ++ tailWord_3750154).sum := by decide
  have hdescent : baseEnd_3750154 < baseStart_3750154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750158 : List Nat := [4, 1, 1, 2, 1, 2, 3, 4, 1, 3]
def baseStart_3750158 : Nat := 118140960795 + 3750158 * 2 ^ 59
def prefixEnd_3750158 : Nat := 4983230072969 + 3 ^ 40 * 3750158 * 2
def baseEnd_3750158 : Nat := 1283755722869229148852229

theorem tailTrace_3750158 : CollatzResearch.WordTrace tailWord_3750158 prefixEnd_3750158 1283755722869229148852229 := by
  unfold tailWord_3750158
  simp only [CollatzResearch.WordTrace]
  refine ⟨17097437393478189605076391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91186332765217011227074085 17097437393478189605076391)
  ·
    refine ⟨25646156090217284407614587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17097437393478189605076391 25646156090217284407614587)
    ·
      refine ⟨38469234135325926611421881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25646156090217284407614587 38469234135325926611421881)
      ·
        refine ⟨28851925601494444958566411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38469234135325926611421881 28851925601494444958566411)
        ·
          refine ⟨43277888402241667437849617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28851925601494444958566411 43277888402241667437849617)
          ·
            refine ⟨32458416301681250578387213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43277888402241667437849617 32458416301681250578387213)
            ·
              refine ⟨12171906113130468966895205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32458416301681250578387213 12171906113130468966895205)
              ·
                refine ⟨2282232396211962931292851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12171906113130468966895205 2282232396211962931292851)
                ·
                  refine ⟨3423348594317944396939277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2282232396211962931292851 3423348594317944396939277)
                  ·
                    refine ⟨1283755722869229148852229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3423348594317944396939277 1283755722869229148852229)
                    ·
                      rfl

theorem cell22_3750158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 4, 1, 3].length) (baseStart_3750158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3750158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3750158 prefixEnd_3750158 := by exact prefixLift 3750158
  have htrace : WordTrace (prefixWord ++ tailWord_3750158) baseStart_3750158 baseEnd_3750158 := by
    simpa [prefixWord, tailWord_3750158, baseEnd_3750158] using wordTrace_append hprefix tailTrace_3750158
  have hstable : (prefixWord ++ tailWord_3750158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750158).length < 2 ^ (prefixWord ++ tailWord_3750158).sum := by decide
  have hdescent : baseEnd_3750158 < baseStart_3750158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750216 : List Nat := [2, 1, 3, 1, 1, 2, 4, 4, 4]
def baseStart_3750216 : Nat := 118140960795 + 3750216 * 2 ^ 59
def prefixEnd_3750216 : Nat := 4983230072969 + 3 ^ 40 * 3750216 * 2
def baseEnd_3750216 : Nat := 427925192484845443634017

theorem tailTrace_3750216 : CollatzResearch.WordTrace tailWord_3750216 prefixEnd_3750216 427925192484845443634017 := by
  unfold tailWord_3750216
  simp only [CollatzResearch.WordTrace]
  refine ⟨68390807290807696373111251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91187743054410261830815001 68390807290807696373111251)
  ·
    refine ⟨102586210936211544559666877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68390807290807696373111251 102586210936211544559666877)
    ·
      refine ⟨38469829101079329209875079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102586210936211544559666877 38469829101079329209875079)
      ·
        refine ⟨57704743651618993814812619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38469829101079329209875079 57704743651618993814812619)
        ·
          refine ⟨86557115477428490722218929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57704743651618993814812619 86557115477428490722218929)
          ·
            refine ⟨64917836608071368041664197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86557115477428490722218929 64917836608071368041664197)
            ·
              refine ⟨12172094364013381507812037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64917836608071368041664197 12172094364013381507812037)
              ·
                refine ⟨2282267693252509032714757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12172094364013381507812037 2282267693252509032714757)
                ·
                  refine ⟨427925192484845443634017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2282267693252509032714757 427925192484845443634017)
                  ·
                    rfl

theorem cell22_3750216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 4, 4].length) (baseStart_3750216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3750216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3750216 prefixEnd_3750216 := by exact prefixLift 3750216
  have htrace : WordTrace (prefixWord ++ tailWord_3750216) baseStart_3750216 baseEnd_3750216 := by
    simpa [prefixWord, tailWord_3750216, baseEnd_3750216] using wordTrace_append hprefix tailTrace_3750216
  have hstable : (prefixWord ++ tailWord_3750216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750216).length < 2 ^ (prefixWord ++ tailWord_3750216).sum := by decide
  have hdescent : baseEnd_3750216 < baseStart_3750216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750244 : List Nat := [2, 3, 1, 1, 3, 1, 3, 8]
def baseStart_3750244 : Nat := 118140960795 + 3750244 * 2 ^ 59
def prefixEnd_3750244 : Nat := 4983230072969 + 3 ^ 40 * 3750244 * 2
def baseEnd_3750244 : Nat := 142642795825194843466885

theorem tailTrace_3750244 : CollatzResearch.WordTrace tailWord_3750244 prefixEnd_3750244 142642795825194843466885 := by
  unfold tailWord_3750244
  simp only [CollatzResearch.WordTrace]
  refine ⟨68391317912756976764120893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91188423883675969018827857 68391317912756976764120893)
  ·
    refine ⟨25646744217283866286545335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68391317912756976764120893 25646744217283866286545335)
    ·
      refine ⟨38470116325925799429818003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25646744217283866286545335 38470116325925799429818003)
      ·
        refine ⟨57705174488888699144727005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38470116325925799429818003 57705174488888699144727005)
        ·
          refine ⟨21639440433333262179272627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57705174488888699144727005 21639440433333262179272627)
          ·
            refine ⟨32459160649999893268908941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21639440433333262179272627 32459160649999893268908941)
            ·
              refine ⟨12172185243749959975840853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32459160649999893268908941 12172185243749959975840853)
              ·
                refine ⟨142642795825194843466885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12172185243749959975840853 142642795825194843466885)
                ·
                  rfl

theorem cell22_3750244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 8].length) (baseStart_3750244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3750244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3750244 prefixEnd_3750244 := by exact prefixLift 3750244
  have htrace : WordTrace (prefixWord ++ tailWord_3750244) baseStart_3750244 baseEnd_3750244 := by
    simpa [prefixWord, tailWord_3750244, baseEnd_3750244] using wordTrace_append hprefix tailTrace_3750244
  have hstable : (prefixWord ++ tailWord_3750244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750244).length < 2 ^ (prefixWord ++ tailWord_3750244).sum := by decide
  have hdescent : baseEnd_3750244 < baseStart_3750244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750250 : List Nat := [3, 1, 3, 3, 1, 3, 1, 3, 4]
def baseStart_3750250 : Nat := 118140960795 + 3750250 * 2 ^ 59
def prefixEnd_3750250 : Nat := 4983230072969 + 3 ^ 40 * 3750250 * 2
def baseEnd_3750250 : Nat := 427929072116457191850649

theorem tailTrace_3750250 : CollatzResearch.WordTrace tailWord_3750250 prefixEnd_3750250 427929072116457191850649 := by
  unfold tailWord_3750250
  simp only [CollatzResearch.WordTrace]
  refine ⟨34195713665873054138240051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91188569775661477701973469 34195713665873054138240051)
  ·
    refine ⟨51293570498809581207360077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34195713665873054138240051 51293570498809581207360077)
    ·
      refine ⟨19235088937053592952760029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51293570498809581207360077 19235088937053592952760029)
      ·
        refine ⟨7213158351395097357285011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19235088937053592952760029 7213158351395097357285011)
        ·
          refine ⟨10819737527092646035927517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7213158351395097357285011 10819737527092646035927517)
          ·
            refine ⟨4057401572659742263472819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10819737527092646035927517 4057401572659742263472819)
            ·
              refine ⟨6086102358989613395209229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4057401572659742263472819 6086102358989613395209229)
              ·
                refine ⟨2282288384621105023203461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6086102358989613395209229 2282288384621105023203461)
                ·
                  refine ⟨427929072116457191850649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2282288384621105023203461 427929072116457191850649)
                  ·
                    rfl

theorem cell22_3750250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 3, 4].length) (baseStart_3750250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3750250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3750250 prefixEnd_3750250 := by exact prefixLift 3750250
  have htrace : WordTrace (prefixWord ++ tailWord_3750250) baseStart_3750250 baseEnd_3750250 := by
    simpa [prefixWord, tailWord_3750250, baseEnd_3750250] using wordTrace_append hprefix tailTrace_3750250
  have hstable : (prefixWord ++ tailWord_3750250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750250).length < 2 ^ (prefixWord ++ tailWord_3750250).sum := by decide
  have hdescent : baseEnd_3750250 < baseStart_3750250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750261 : List Nat := [1, 3, 4, 1, 2, 3, 8]
def baseStart_3750261 : Nat := 118140960795 + 3750261 * 2 ^ 59
def prefixEnd_3750261 : Nat := 4983230072969 + 3 ^ 40 * 3750261 * 2
def baseEnd_3750261 : Nat := 47547814143487822723219

theorem tailTrace_3750261 : CollatzResearch.WordTrace tailWord_3750261 prefixEnd_3750261 47547814143487822723219 := by
  unfold tailWord_3750261
  simp only [CollatzResearch.WordTrace]
  refine ⟨136783255866452365431610637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91188837244301576954407091 136783255866452365431610637)
  ·
    refine ⟨51293720949919637036853989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136783255866452365431610637 51293720949919637036853989)
    ·
      refine ⟨9617572678109931944410123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51293720949919637036853989 9617572678109931944410123)
      ·
        refine ⟨14426359017164897916615185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9617572678109931944410123 14426359017164897916615185)
        ·
          refine ⟨10819769262873673437461389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14426359017164897916615185 10819769262873673437461389)
          ·
            refine ⟨4057413473577627539048021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10819769262873673437461389 4057413473577627539048021)
            ·
              refine ⟨47547814143487822723219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4057413473577627539048021 47547814143487822723219)
              ·
                rfl

theorem cell22_3750261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 8].length) (baseStart_3750261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3750261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3750261 prefixEnd_3750261 := by exact prefixLift 3750261
  have htrace : WordTrace (prefixWord ++ tailWord_3750261) baseStart_3750261 baseEnd_3750261 := by
    simpa [prefixWord, tailWord_3750261, baseEnd_3750261] using wordTrace_append hprefix tailTrace_3750261
  have hstable : (prefixWord ++ tailWord_3750261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750261).length < 2 ^ (prefixWord ++ tailWord_3750261).sum := by decide
  have hdescent : baseEnd_3750261 < baseStart_3750261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750327 : List Nat := [1, 1, 3, 1, 3, 5, 2, 2, 1, 3]
def baseStart_3750327 : Nat := 118140960795 + 3750327 * 2 ^ 59
def prefixEnd_3750327 : Nat := 4983230072969 + 3 ^ 40 * 3750327 * 2
def baseEnd_3750327 : Nat := 1283813575022969041376711

theorem tailTrace_3750327 : CollatzResearch.WordTrace tailWord_3750327 prefixEnd_3750327 1283813575022969041376711 := by
  unfold tailWord_3750327
  simp only [CollatzResearch.WordTrace]
  refine ⟨136785663084213258703513235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91190442056142172469008823 136785663084213258703513235)
  ·
    refine ⟨205178494626319888055269853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136785663084213258703513235 205178494626319888055269853)
    ·
      refine ⟨76941935484869958020726195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205178494626319888055269853 76941935484869958020726195)
      ·
        refine ⟨115412903227304937031089293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76941935484869958020726195 115412903227304937031089293)
        ·
          refine ⟨43279838710239351386658485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115412903227304937031089293 43279838710239351386658485)
          ·
            refine ⟨4057484879084939192499233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43279838710239351386658485 4057484879084939192499233)
            ·
              refine ⟨3043113659313704394374425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4057484879084939192499233 3043113659313704394374425)
              ·
                refine ⟨2282335244485278295780819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3043113659313704394374425 2282335244485278295780819)
                ·
                  refine ⟨3423502866727917443671229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2282335244485278295780819 3423502866727917443671229)
                  ·
                    refine ⟨1283813575022969041376711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3423502866727917443671229 1283813575022969041376711)
                    ·
                      rfl

theorem cell22_3750327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 2, 2, 1, 3].length) (baseStart_3750327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3750327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3750327 prefixEnd_3750327 := by exact prefixLift 3750327
  have htrace : WordTrace (prefixWord ++ tailWord_3750327) baseStart_3750327 baseEnd_3750327 := by
    simpa [prefixWord, tailWord_3750327, baseEnd_3750327] using wordTrace_append hprefix tailTrace_3750327
  have hstable : (prefixWord ++ tailWord_3750327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750327).length < 2 ^ (prefixWord ++ tailWord_3750327).sum := by decide
  have hdescent : baseEnd_3750327 < baseStart_3750327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750368 : List Nat := [2, 1, 1, 3, 1, 1, 6, 3, 4]
def baseStart_3750368 : Nat := 118140960795 + 3750368 * 2 ^ 59
def prefixEnd_3750368 : Nat := 4983230072969 + 3 ^ 40 * 3750368 * 2
def baseEnd_3750368 : Nat := 427942536720286200367195

theorem tailTrace_3750368 : CollatzResearch.WordTrace tailWord_3750368 prefixEnd_3750368 427942536720286200367195 := by
  unfold tailWord_3750368
  simp only [CollatzResearch.WordTrace]
  refine ⟨68393579238532361352877879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91191438984709815137170505 68393579238532361352877879)
  ·
    refine ⟨102590368857798542029316819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68393579238532361352877879 102590368857798542029316819)
    ·
      refine ⟨153885553286697813043975229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102590368857798542029316819 153885553286697813043975229)
      ·
        refine ⟨57707082482511679891490711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153885553286697813043975229 57707082482511679891490711)
        ·
          refine ⟨86560623723767519837236067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57707082482511679891490711 86560623723767519837236067)
          ·
            refine ⟨129840935585651279755854101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86560623723767519837236067 129840935585651279755854101)
            ·
              refine ⟨6086293855577403738555661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 129840935585651279755854101 6086293855577403738555661)
              ·
                refine ⟨2282360195841526401958373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6086293855577403738555661 2282360195841526401958373)
                ·
                  refine ⟨427942536720286200367195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2282360195841526401958373 427942536720286200367195)
                  ·
                    rfl

theorem cell22_3750368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 3, 4].length) (baseStart_3750368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3750368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3750368 prefixEnd_3750368 := by exact prefixLift 3750368
  have htrace : WordTrace (prefixWord ++ tailWord_3750368) baseStart_3750368 baseEnd_3750368 := by
    simpa [prefixWord, tailWord_3750368, baseEnd_3750368] using wordTrace_append hprefix tailTrace_3750368
  have hstable : (prefixWord ++ tailWord_3750368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750368).length < 2 ^ (prefixWord ++ tailWord_3750368).sum := by decide
  have hdescent : baseEnd_3750368 < baseStart_3750368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750379 : List Nat := [1, 1, 1, 1, 2, 3, 13]
def baseStart_3750379 : Nat := 118140960795 + 3750379 * 2 ^ 59
def prefixEnd_3750379 : Nat := 4983230072969 + 3 ^ 40 * 3750379 * 2
def baseEnd_3750379 : Nat := 47549310210579934780613

theorem tailTrace_3750379 : CollatzResearch.WordTrace tailWord_3750379 prefixEnd_3750379 47549310210579934780613 := by
  unfold tailWord_3750379
  simp only [CollatzResearch.WordTrace]
  refine ⟨136787559680024871584406191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91191706453349914389604127 136787559680024871584406191)
  ·
    refine ⟨205181339520037307376609287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136787559680024871584406191 205181339520037307376609287)
    ·
      refine ⟨307772009280055961064913931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205181339520037307376609287 307772009280055961064913931)
      ·
        refine ⟨461658013920083941597370897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307772009280055961064913931 461658013920083941597370897)
        ·
          refine ⟨346243510440062956198028173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 461658013920083941597370897 346243510440062956198028173)
          ·
            refine ⟨129841316415023608574260565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 346243510440062956198028173 129841316415023608574260565)
            ·
              refine ⟨47549310210579934780613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 129841316415023608574260565 47549310210579934780613)
              ·
                rfl

theorem cell22_3750379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 13].length) (baseStart_3750379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3750379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3750379 prefixEnd_3750379 := by exact prefixLift 3750379
  have htrace : WordTrace (prefixWord ++ tailWord_3750379) baseStart_3750379 baseEnd_3750379 := by
    simpa [prefixWord, tailWord_3750379, baseEnd_3750379] using wordTrace_append hprefix tailTrace_3750379
  have hstable : (prefixWord ++ tailWord_3750379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750379).length < 2 ^ (prefixWord ++ tailWord_3750379).sum := by decide
  have hdescent : baseEnd_3750379 < baseStart_3750379 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750456 : List Nat := [2, 1, 2, 1, 4, 1, 2, 1, 1, 7]
def baseStart_3750456 : Nat := 118140960795 + 3750456 * 2 ^ 59
def prefixEnd_3750456 : Nat := 4983230072969 + 3 ^ 40 * 3750456 * 2
def baseEnd_3750456 : Nat := 1283857734359255704901315

theorem tailTrace_3750456 : CollatzResearch.WordTrace tailWord_3750456 prefixEnd_3750456 1283857734359255704901315 := by
  unfold tailWord_3750456
  simp only [CollatzResearch.WordTrace]
  refine ⟨68395184050372956867479611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91193578733830609156639481 68395184050372956867479611)
  ·
    refine ⟨102592776075559435301219417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68395184050372956867479611 102592776075559435301219417)
    ·
      refine ⟨76944582056669576475914563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102592776075559435301219417 76944582056669576475914563)
      ·
        refine ⟨115416873085004364713871845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76944582056669576475914563 115416873085004364713871845)
        ·
          refine ⟨21640663703438318383850971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115416873085004364713871845 21640663703438318383850971)
          ·
            refine ⟨32460995555157477575776457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21640663703438318383850971 32460995555157477575776457)
            ·
              refine ⟨24345746666368108181832343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32460995555157477575776457 24345746666368108181832343)
              ·
                refine ⟨36518619999552162272748515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24345746666368108181832343 36518619999552162272748515)
                ·
                  refine ⟨54777929999328243409122773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36518619999552162272748515 54777929999328243409122773)
                  ·
                    refine ⟨1283857734359255704901315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54777929999328243409122773 1283857734359255704901315)
                    ·
                      rfl

theorem cell22_3750456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 1, 7].length) (baseStart_3750456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3750456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3750456 prefixEnd_3750456 := by exact prefixLift 3750456
  have htrace : WordTrace (prefixWord ++ tailWord_3750456) baseStart_3750456 baseEnd_3750456 := by
    simpa [prefixWord, tailWord_3750456, baseEnd_3750456] using wordTrace_append hprefix tailTrace_3750456
  have hstable : (prefixWord ++ tailWord_3750456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750456).length < 2 ^ (prefixWord ++ tailWord_3750456).sum := by decide
  have hdescent : baseEnd_3750456 < baseStart_3750456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750458 : List Nat := [3, 1, 1, 1, 3, 4, 1, 3, 5]
def baseStart_3750458 : Nat := 118140960795 + 3750458 * 2 ^ 59
def prefixEnd_3750458 : Nat := 4983230072969 + 3 ^ 40 * 3750458 * 2
def baseEnd_3750458 : Nat := 427952806333376122117103

theorem tailTrace_3750458 : CollatzResearch.WordTrace tailWord_3750458 prefixEnd_3750458 427952806333376122117103 := by
  unfold tailWord_3750458
  simp only [CollatzResearch.WordTrace]
  refine ⟨34197610261684667019133007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91193627364492445384354685 34197610261684667019133007)
  ·
    refine ⟨51296415392527000528699511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34197610261684667019133007 51296415392527000528699511)
    ·
      refine ⟨76944623088790500793049267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51296415392527000528699511 76944623088790500793049267)
      ·
        refine ⟨115416934633185751189573901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76944623088790500793049267 115416934633185751189573901)
        ·
          refine ⟨43281350487444656696090213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115416934633185751189573901 43281350487444656696090213)
          ·
            refine ⟨8115253216395873130516915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43281350487444656696090213 8115253216395873130516915)
            ·
              refine ⟨12172879824593809695775373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8115253216395873130516915 12172879824593809695775373)
              ·
                refine ⟨4564829934222678635915765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12172879824593809695775373 4564829934222678635915765)
                ·
                  refine ⟨427952806333376122117103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4564829934222678635915765 427952806333376122117103)
                  ·
                    rfl

theorem cell22_3750458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 3, 5].length) (baseStart_3750458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3750458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3750458 prefixEnd_3750458 := by exact prefixLift 3750458
  have htrace : WordTrace (prefixWord ++ tailWord_3750458) baseStart_3750458 baseEnd_3750458 := by
    simpa [prefixWord, tailWord_3750458, baseEnd_3750458] using wordTrace_append hprefix tailTrace_3750458
  have hstable : (prefixWord ++ tailWord_3750458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750458).length < 2 ^ (prefixWord ++ tailWord_3750458).sum := by decide
  have hdescent : baseEnd_3750458 < baseStart_3750458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750488 : List Nat := [2, 1, 2, 2, 1, 2, 2, 5, 1, 4]
def baseStart_3750488 : Nat := 118140960795 + 3750488 * 2 ^ 59
def prefixEnd_3750488 : Nat := 4983230072969 + 3 ^ 40 * 3750488 * 2
def baseEnd_3750488 : Nat := 1283868688613218288101217

theorem tailTrace_3750488 : CollatzResearch.WordTrace tailWord_3750488 prefixEnd_3750488 1283868688613218288101217 := by
  unfold tailWord_3750488
  simp only [CollatzResearch.WordTrace]
  refine ⟨68395767618314991600062059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91194356824419988800082745 68395767618314991600062059)
  ·
    refine ⟨102593651427472487400093089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68395767618314991600062059 102593651427472487400093089)
    ·
      refine ⟨76945238570604365550069817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102593651427472487400093089 76945238570604365550069817)
      ·
        refine ⟨57708928927953274162552363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76945238570604365550069817 57708928927953274162552363)
        ·
          refine ⟨86563393391929911243828545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57708928927953274162552363 86563393391929911243828545)
          ·
            refine ⟨64922545043947433432871409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86563393391929911243828545 64922545043947433432871409)
            ·
              refine ⟨48691908782960575074653557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64922545043947433432871409 48691908782960575074653557)
              ·
                refine ⟨4564866448402553913248771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48691908782960575074653557 4564866448402553913248771)
                ·
                  refine ⟨6847299672603830869873157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4564866448402553913248771 6847299672603830869873157)
                  ·
                    refine ⟨1283868688613218288101217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6847299672603830869873157 1283868688613218288101217)
                    ·
                      rfl

theorem cell22_3750488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 5, 1, 4].length) (baseStart_3750488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3750488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3750488 prefixEnd_3750488 := by exact prefixLift 3750488
  have htrace : WordTrace (prefixWord ++ tailWord_3750488) baseStart_3750488 baseEnd_3750488 := by
    simpa [prefixWord, tailWord_3750488, baseEnd_3750488] using wordTrace_append hprefix tailTrace_3750488
  have hstable : (prefixWord ++ tailWord_3750488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750488).length < 2 ^ (prefixWord ++ tailWord_3750488).sum := by decide
  have hdescent : baseEnd_3750488 < baseStart_3750488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750531 : List Nat := [1, 1, 1, 3, 3, 1, 2, 10]
def baseStart_3750531 : Nat := 118140960795 + 3750531 * 2 ^ 59
def prefixEnd_3750531 : Nat := 4983230072969 + 3 ^ 40 * 3750531 * 2
def baseEnd_3750531 : Nat := 142653712043553389919565

theorem tailTrace_3750531 : CollatzResearch.WordTrace tailWord_3750531 prefixEnd_3750531 142653712043553389919565 := by
  unfold tailWord_3750531
  simp only [CollatzResearch.WordTrace]
  refine ⟨136793103575474201543939447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91195402383649467695959631 136793103575474201543939447)
  ·
    refine ⟨205189655363211302315909171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136793103575474201543939447 205189655363211302315909171)
    ·
      refine ⟨307784483044816953473863757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205189655363211302315909171 307784483044816953473863757)
      ·
        refine ⟨115419181141806357552698909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 307784483044816953473863757 115419181141806357552698909)
        ·
          refine ⟨43282192928177384082262091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115419181141806357552698909 43282192928177384082262091)
          ·
            refine ⟨64923289392266076123393137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43282192928177384082262091 64923289392266076123393137)
            ·
              refine ⟨48692467044199557092544853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64923289392266076123393137 48692467044199557092544853)
              ·
                refine ⟨142653712043553389919565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 48692467044199557092544853 142653712043553389919565)
                ·
                  rfl

theorem cell22_3750531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 10].length) (baseStart_3750531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3750531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3750531 prefixEnd_3750531 := by exact prefixLift 3750531
  have htrace : WordTrace (prefixWord ++ tailWord_3750531) baseStart_3750531 baseEnd_3750531 := by
    simpa [prefixWord, tailWord_3750531, baseEnd_3750531] using wordTrace_append hprefix tailTrace_3750531
  have hstable : (prefixWord ++ tailWord_3750531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750531).length < 2 ^ (prefixWord ++ tailWord_3750531).sum := by decide
  have hdescent : baseEnd_3750531 < baseStart_3750531 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750533 : List Nat := [1, 3, 1, 1, 4, 3, 1, 1, 1, 6]
def baseStart_3750533 : Nat := 118140960795 + 3750533 * 2 ^ 59
def prefixEnd_3750533 : Nat := 4983230072969 + 3 ^ 40 * 3750533 * 2
def baseEnd_3750533 : Nat := 1283884093032853170726079

theorem tailTrace_3750533 : CollatzResearch.WordTrace tailWord_3750533 prefixEnd_3750533 1283884093032853170726079 := by
  unfold tailWord_3750533
  simp only [CollatzResearch.WordTrace]
  refine ⟨136793176521466955885512253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91195451014311303923674835 136793176521466955885512253)
  ·
    refine ⟨51297441195550108457067095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136793176521466955885512253 51297441195550108457067095)
    ·
      refine ⟨76946161793325162685600643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51297441195550108457067095 76946161793325162685600643)
      ·
        refine ⟨115419242689987744028400965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76946161793325162685600643 115419242689987744028400965)
        ·
          refine ⟨21641108004372702005325181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115419242689987744028400965 21641108004372702005325181)
          ·
            refine ⟨8115415501639763251996943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21641108004372702005325181 8115415501639763251996943)
            ·
              refine ⟨12173123252459644877995415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8115415501639763251996943 12173123252459644877995415)
              ·
                refine ⟨18259684878689467316993123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12173123252459644877995415 18259684878689467316993123)
                ·
                  refine ⟨27389527318034200975489685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18259684878689467316993123 27389527318034200975489685)
                  ·
                    refine ⟨1283884093032853170726079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27389527318034200975489685 1283884093032853170726079)
                    ·
                      rfl

theorem cell22_3750533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 6].length) (baseStart_3750533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3750533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3750533 prefixEnd_3750533 := by exact prefixLift 3750533
  have htrace : WordTrace (prefixWord ++ tailWord_3750533) baseStart_3750533 baseEnd_3750533 := by
    simpa [prefixWord, tailWord_3750533, baseEnd_3750533] using wordTrace_append hprefix tailTrace_3750533
  have hstable : (prefixWord ++ tailWord_3750533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750533).length < 2 ^ (prefixWord ++ tailWord_3750533).sum := by decide
  have hdescent : baseEnd_3750533 < baseStart_3750533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750582 : List Nat := [5, 1, 3, 1, 2, 1, 1, 8]
def baseStart_3750582 : Nat := 118140960795 + 3750582 * 2 ^ 59
def prefixEnd_3750582 : Nat := 4983230072969 + 3 ^ 40 * 3750582 * 2
def baseEnd_3750582 : Nat := 142655651859359264027881

theorem tailTrace_3750582 : CollatzResearch.WordTrace tailWord_3750582 prefixEnd_3750582 142655651859359264027881 := by
  unfold tailWord_3750582
  simp only [CollatzResearch.WordTrace]
  refine ⟨8549685231143089828377875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91196642465526291502697333 8549685231143089828377875)
  ·
    refine ⟨12824527846714634742566813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8549685231143089828377875 12824527846714634742566813)
    ·
      refine ⟨4809197942517988028462555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12824527846714634742566813 4809197942517988028462555)
      ·
        refine ⟨7213796913776982042693833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4809197942517988028462555 7213796913776982042693833)
        ·
          refine ⟨5410347685332736532020375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7213796913776982042693833 5410347685332736532020375)
          ·
            refine ⟨8115521527999104798030563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5410347685332736532020375 8115521527999104798030563)
            ·
              refine ⟨12173282291998657197045845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8115521527999104798030563 12173282291998657197045845)
              ·
                refine ⟨142655651859359264027881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12173282291998657197045845 142655651859359264027881)
                ·
                  rfl

theorem cell22_3750582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 8].length) (baseStart_3750582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3750582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3750582 prefixEnd_3750582 := by exact prefixLift 3750582
  have htrace : WordTrace (prefixWord ++ tailWord_3750582) baseStart_3750582 baseEnd_3750582 := by
    simpa [prefixWord, tailWord_3750582, baseEnd_3750582] using wordTrace_append hprefix tailTrace_3750582
  have hstable : (prefixWord ++ tailWord_3750582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750582).length < 2 ^ (prefixWord ++ tailWord_3750582).sum := by decide
  have hdescent : baseEnd_3750582 < baseStart_3750582 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750627 : List Nat := [1, 1, 1, 7, 1, 1, 4, 1, 5]
def baseStart_3750627 : Nat := 118140960795 + 3750627 * 2 ^ 59
def prefixEnd_3750627 : Nat := 4983230072969 + 3 ^ 40 * 3750627 * 2
def baseEnd_3750627 : Nat := 427972090384622752958597

theorem tailTrace_3750627 : CollatzResearch.WordTrace tailWord_3750627 prefixEnd_3750627 427972090384622752958597 := by
  unfold tailWord_3750627
  simp only [CollatzResearch.WordTrace]
  refine ⟨136796604983126409939434135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91197736655417606626289423 136796604983126409939434135)
  ·
    refine ⟨205194907474689614909151203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136796604983126409939434135 205194907474689614909151203)
    ·
      refine ⟨307792361212034422363726805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205194907474689614909151203 307792361212034422363726805)
      ·
        refine ⟨7213883465907056774149847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 307792361212034422363726805 7213883465907056774149847)
        ·
          refine ⟨10820825198860585161224771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7213883465907056774149847 10820825198860585161224771)
          ·
            refine ⟨16231237798290877741837157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10820825198860585161224771 16231237798290877741837157)
            ·
              refine ⟨3043357087179539576594467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16231237798290877741837157 3043357087179539576594467)
              ·
                refine ⟨4565035630769309364891701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3043357087179539576594467 4565035630769309364891701)
                ·
                  refine ⟨427972090384622752958597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4565035630769309364891701 427972090384622752958597)
                  ·
                    rfl

theorem cell22_3750627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 4, 1, 5].length) (baseStart_3750627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3750627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3750627 prefixEnd_3750627 := by exact prefixLift 3750627
  have htrace : WordTrace (prefixWord ++ tailWord_3750627) baseStart_3750627 baseEnd_3750627 := by
    simpa [prefixWord, tailWord_3750627, baseEnd_3750627] using wordTrace_append hprefix tailTrace_3750627
  have hstable : (prefixWord ++ tailWord_3750627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750627).length < 2 ^ (prefixWord ++ tailWord_3750627).sum := by decide
  have hdescent : baseEnd_3750627 < baseStart_3750627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750655 : List Nat := [1, 1, 2, 2, 1, 3, 1, 7, 4]
def baseStart_3750655 : Nat := 118140960795 + 3750655 * 2 ^ 59
def prefixEnd_3750655 : Nat := 4983230072969 + 3 ^ 40 * 3750655 * 2
def baseEnd_3750655 : Nat := 427975285375361839725235

theorem tailTrace_3750655 : CollatzResearch.WordTrace tailWord_3750655 prefixEnd_3750655 427975285375361839725235 := by
  unfold tailWord_3750655
  simp only [CollatzResearch.WordTrace]
  refine ⟨136797626227024970721453419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91198417484683313814302279 136797626227024970721453419)
  ·
    refine ⟨205196439340537456082180129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136797626227024970721453419 205196439340537456082180129)
    ·
      refine ⟨153897329505403092061635097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205196439340537456082180129 153897329505403092061635097)
      ·
        refine ⟨115422997129052319046226323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153897329505403092061635097 115422997129052319046226323)
        ·
          refine ⟨173134495693578478569339485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115422997129052319046226323 173134495693578478569339485)
          ·
            refine ⟨64925435885091929463502307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173134495693578478569339485 64925435885091929463502307)
            ·
              refine ⟨97388153827637894195253461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64925435885091929463502307 97388153827637894195253461)
              ·
                refine ⟨2282534855335263145201253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 97388153827637894195253461 2282534855335263145201253)
                ·
                  refine ⟨427975285375361839725235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2282534855335263145201253 427975285375361839725235)
                  ·
                    rfl

theorem cell22_3750655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 7, 4].length) (baseStart_3750655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3750655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3750655 prefixEnd_3750655 := by exact prefixLift 3750655
  have htrace : WordTrace (prefixWord ++ tailWord_3750655) baseStart_3750655 baseEnd_3750655 := by
    simpa [prefixWord, tailWord_3750655, baseEnd_3750655] using wordTrace_append hprefix tailTrace_3750655
  have hstable : (prefixWord ++ tailWord_3750655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750655).length < 2 ^ (prefixWord ++ tailWord_3750655).sum := by decide
  have hdescent : baseEnd_3750655 < baseStart_3750655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750668 : List Nat := [2, 2, 1, 2, 2, 1, 1, 2, 3, 6]
def baseStart_3750668 : Nat := 118140960795 + 3750668 * 2 ^ 59
def prefixEnd_3750668 : Nat := 4983230072969 + 3 ^ 40 * 3750668 * 2
def baseEnd_3750668 : Nat := 1283930306291757818600665

theorem tailTrace_3750668 : CollatzResearch.WordTrace tailWord_3750668 prefixEnd_3750668 1283930306291757818600665 := by
  unfold tailWord_3750668
  simp only [CollatzResearch.WordTrace]
  refine ⟨68399050187988936970838329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91198733583985249294451105 68399050187988936970838329)
  ·
    refine ⟨51299287640991702728128747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68399050187988936970838329 51299287640991702728128747)
    ·
      refine ⟨76948931461487554092193121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51299287640991702728128747 76948931461487554092193121)
      ·
        refine ⟨57711698596115665569144841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76948931461487554092193121 57711698596115665569144841)
        ·
          refine ⟨43283773947086749176858631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57711698596115665569144841 43283773947086749176858631)
          ·
            refine ⟨64925660920630123765287947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43283773947086749176858631 64925660920630123765287947)
            ·
              refine ⟨97388491380945185647931921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64925660920630123765287947 97388491380945185647931921)
              ·
                refine ⟨73041368535708889235948941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97388491380945185647931921 73041368535708889235948941)
                ·
                  refine ⟨27390513200890833463480853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73041368535708889235948941 27390513200890833463480853)
                  ·
                    refine ⟨1283930306291757818600665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27390513200890833463480853 1283930306291757818600665)
                    ·
                      rfl

theorem cell22_3750668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 3, 6].length) (baseStart_3750668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3750668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3750668 prefixEnd_3750668 := by exact prefixLift 3750668
  have htrace : WordTrace (prefixWord ++ tailWord_3750668) baseStart_3750668 baseEnd_3750668 := by
    simpa [prefixWord, tailWord_3750668, baseEnd_3750668] using wordTrace_append hprefix tailTrace_3750668
  have hstable : (prefixWord ++ tailWord_3750668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750668).length < 2 ^ (prefixWord ++ tailWord_3750668).sum := by decide
  have hdescent : baseEnd_3750668 < baseStart_3750668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750687 : List Nat := [1, 1, 2, 4, 2, 2, 2, 3, 2, 3]
def baseStart_3750687 : Nat := 118140960795 + 3750687 * 2 ^ 59
def prefixEnd_3750687 : Nat := 4983230072969 + 3 ^ 40 * 3750687 * 2
def baseEnd_3750687 : Nat := 1283936810380048102375607

theorem tailTrace_3750687 : CollatzResearch.WordTrace tailWord_3750687 prefixEnd_3750687 1283936810380048102375607 := by
  unfold tailWord_3750687
  simp only [CollatzResearch.WordTrace]
  refine ⟨136798793362909040186618315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91199195575272693457745543 136798793362909040186618315)
  ·
    refine ⟨205198190044363560279927473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136798793362909040186618315 205198190044363560279927473)
    ·
      refine ⟨153898642533272670209945605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205198190044363560279927473 153898642533272670209945605)
      ·
        refine ⟨28855995474988625664364801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153898642533272670209945605 28855995474988625664364801)
        ·
          refine ⟨21641996606241469248273601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28855995474988625664364801 21641996606241469248273601)
          ·
            refine ⟨16231497454681101936205201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21641996606241469248273601 16231497454681101936205201)
            ·
              refine ⟨12173623091010826452153901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16231497454681101936205201 12173623091010826452153901)
              ·
                refine ⟨4565108659129059919557713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12173623091010826452153901 4565108659129059919557713)
                ·
                  refine ⟨3423831494346794939668285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4565108659129059919557713 3423831494346794939668285)
                  ·
                    refine ⟨1283936810380048102375607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3423831494346794939668285 1283936810380048102375607)
                    ·
                      rfl

theorem cell22_3750687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 3, 2, 3].length) (baseStart_3750687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3750687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3750687 prefixEnd_3750687 := by exact prefixLift 3750687
  have htrace : WordTrace (prefixWord ++ tailWord_3750687) baseStart_3750687 baseEnd_3750687 := by
    simpa [prefixWord, tailWord_3750687, baseEnd_3750687] using wordTrace_append hprefix tailTrace_3750687
  have hstable : (prefixWord ++ tailWord_3750687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750687).length < 2 ^ (prefixWord ++ tailWord_3750687).sum := by decide
  have hdescent : baseEnd_3750687 < baseStart_3750687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750700 : List Nat := [2, 2, 1, 1, 1, 4, 5, 6]
def baseStart_3750700 : Nat := 118140960795 + 3750700 * 2 ^ 59
def prefixEnd_3750700 : Nat := 4983230072969 + 3 ^ 40 * 3750700 * 2
def baseEnd_3750700 : Nat := 142660140060635600200063

theorem tailTrace_3750700 : CollatzResearch.WordTrace tailWord_3750700 prefixEnd_3750700 142660140060635600200063 := by
  unfold tailWord_3750700
  simp only [CollatzResearch.WordTrace]
  refine ⟨68399633755930971703420777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91199511674574628937894369 68399633755930971703420777)
  ·
    refine ⟨51299725316948228777565583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68399633755930971703420777 51299725316948228777565583)
    ·
      refine ⟨76949587975422343166348375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51299725316948228777565583 76949587975422343166348375)
      ·
        refine ⟨115424381963133514749522563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76949587975422343166348375 115424381963133514749522563)
        ·
          refine ⟨173136572944700272124283845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115424381963133514749522563 173136572944700272124283845)
          ·
            refine ⟨32463107427131301023303221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 173136572944700272124283845 32463107427131301023303221)
            ·
              refine ⟨3043416321293559470934677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32463107427131301023303221 3043416321293559470934677)
              ·
                refine ⟨142660140060635600200063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3043416321293559470934677 142660140060635600200063)
                ·
                  rfl

theorem cell22_3750700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 5, 6].length) (baseStart_3750700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3750700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3750700 prefixEnd_3750700 := by exact prefixLift 3750700
  have htrace : WordTrace (prefixWord ++ tailWord_3750700) baseStart_3750700 baseEnd_3750700 := by
    simpa [prefixWord, tailWord_3750700, baseEnd_3750700] using wordTrace_append hprefix tailTrace_3750700
  have hstable : (prefixWord ++ tailWord_3750700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750700).length < 2 ^ (prefixWord ++ tailWord_3750700).sum := by decide
  have hdescent : baseEnd_3750700 < baseStart_3750700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750702 : List Nat := [4, 1, 3, 2, 1, 2, 1, 1, 1, 6]
def baseStart_3750702 : Nat := 118140960795 + 3750702 * 2 ^ 59
def prefixEnd_3750702 : Nat := 4983230072969 + 3 ^ 40 * 3750702 * 2
def baseEnd_3750702 : Nat := 1283941945186593063250561

theorem tailTrace_3750702 : CollatzResearch.WordTrace tailWord_3750702 prefixEnd_3750702 1283941945186593063250561 := by
  unfold tailWord_3750702
  simp only [CollatzResearch.WordTrace]
  refine ⟨17099917557231837218551795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91199560305236465165609573 17099917557231837218551795)
  ·
    refine ⟨25649876335847755827827693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17099917557231837218551795 25649876335847755827827693)
    ·
      refine ⟨9618703625942908435435385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25649876335847755827827693 9618703625942908435435385)
      ·
        refine ⟨7214027719457181326576539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9618703625942908435435385 7214027719457181326576539)
        ·
          refine ⟨10821041579185771989864809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7214027719457181326576539 10821041579185771989864809)
          ·
            refine ⟨8115781184389328992398607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10821041579185771989864809 8115781184389328992398607)
            ·
              refine ⟨12173671776583993488597911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8115781184389328992398607 12173671776583993488597911)
              ·
                refine ⟨18260507664875990232896867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12173671776583993488597911 18260507664875990232896867)
                ·
                  refine ⟨27390761497313985349345301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18260507664875990232896867 27390761497313985349345301)
                  ·
                    refine ⟨1283941945186593063250561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27390761497313985349345301 1283941945186593063250561)
                    ·
                      rfl

theorem cell22_3750702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_3750702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3750702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3750702 prefixEnd_3750702 := by exact prefixLift 3750702
  have htrace : WordTrace (prefixWord ++ tailWord_3750702) baseStart_3750702 baseEnd_3750702 := by
    simpa [prefixWord, tailWord_3750702, baseEnd_3750702] using wordTrace_append hprefix tailTrace_3750702
  have hstable : (prefixWord ++ tailWord_3750702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750702).length < 2 ^ (prefixWord ++ tailWord_3750702).sum := by decide
  have hdescent : baseEnd_3750702 < baseStart_3750702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750708 : List Nat := [2, 5, 1, 1, 4, 1, 2, 1, 1, 4]
def baseStart_3750708 : Nat := 118140960795 + 3750708 * 2 ^ 59
def prefixEnd_3750708 : Nat := 4983230072969 + 3 ^ 40 * 3750708 * 2
def baseEnd_3750708 : Nat := 1283943999109211047600543

theorem tailTrace_3750708 : CollatzResearch.WordTrace tailWord_3750708 prefixEnd_3750708 1283943999109211047600543 := by
  unfold tailWord_3750708
  simp only [CollatzResearch.WordTrace]
  refine ⟨68399779647916480386566389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91199706197221973848755185 68399779647916480386566389)
  ·
    refine ⟨6412479341992170036240599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68399779647916480386566389 6412479341992170036240599)
    ·
      refine ⟨9618719012988255054360899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6412479341992170036240599 9618719012988255054360899)
      ·
        refine ⟨14428078519482382581541349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9618719012988255054360899 14428078519482382581541349)
        ·
          refine ⟨2705264722402946734039003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14428078519482382581541349 2705264722402946734039003)
          ·
            refine ⟨4057897083604420101058505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2705264722402946734039003 4057897083604420101058505)
            ·
              refine ⟨3043422812703315075793879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4057897083604420101058505 3043422812703315075793879)
              ·
                refine ⟨4565134219054972613690819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3043422812703315075793879 4565134219054972613690819)
                ·
                  refine ⟨6847701328582458920536229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4565134219054972613690819 6847701328582458920536229)
                  ·
                    refine ⟨1283943999109211047600543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6847701328582458920536229 1283943999109211047600543)
                    ·
                      rfl

theorem cell22_3750708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_3750708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3750708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3750708 prefixEnd_3750708 := by exact prefixLift 3750708
  have htrace : WordTrace (prefixWord ++ tailWord_3750708) baseStart_3750708 baseEnd_3750708 := by
    simpa [prefixWord, tailWord_3750708, baseEnd_3750708] using wordTrace_append hprefix tailTrace_3750708
  have hstable : (prefixWord ++ tailWord_3750708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750708).length < 2 ^ (prefixWord ++ tailWord_3750708).sum := by decide
  have hdescent : baseEnd_3750708 < baseStart_3750708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750732 : List Nat := [2, 2, 1, 3, 3, 1, 1, 3, 3, 3]
def baseStart_3750732 : Nat := 118140960795 + 3750732 * 2 ^ 59
def prefixEnd_3750732 : Nat := 4983230072969 + 3 ^ 40 * 3750732 * 2
def baseEnd_3750732 : Nat := 1283952214799682985000469

theorem tailTrace_3750732 : CollatzResearch.WordTrace tailWord_3750732 prefixEnd_3750732 1283952214799682985000469 := by
  unfold tailWord_3750732
  simp only [CollatzResearch.WordTrace]
  refine ⟨68400217323873006436003225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91200289765164008581337633 68400217323873006436003225)
  ·
    refine ⟨51300162992904754827002419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68400217323873006436003225 51300162992904754827002419)
    ·
      refine ⟨76950244489357132240503629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51300162992904754827002419 76950244489357132240503629)
      ·
        refine ⟨28856341683508924590188861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76950244489357132240503629 28856341683508924590188861)
        ·
          refine ⟨10821128131315846721320823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28856341683508924590188861 10821128131315846721320823)
          ·
            refine ⟨16231692196973770081981235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10821128131315846721320823 16231692196973770081981235)
            ·
              refine ⟨24347538295460655122971853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16231692196973770081981235 24347538295460655122971853)
              ·
                refine ⟨9130326860797745671114445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24347538295460655122971853 9130326860797745671114445)
                ·
                  refine ⟨3423872572799154626667917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9130326860797745671114445 3423872572799154626667917)
                  ·
                    refine ⟨1283952214799682985000469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3423872572799154626667917 1283952214799682985000469)
                    ·
                      rfl

theorem cell22_3750732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 3, 3, 3].length) (baseStart_3750732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3750732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3750732 prefixEnd_3750732 := by exact prefixLift 3750732
  have htrace : WordTrace (prefixWord ++ tailWord_3750732) baseStart_3750732 baseEnd_3750732 := by
    simpa [prefixWord, tailWord_3750732, baseEnd_3750732] using wordTrace_append hprefix tailTrace_3750732
  have hstable : (prefixWord ++ tailWord_3750732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750732).length < 2 ^ (prefixWord ++ tailWord_3750732).sum := by decide
  have hdescent : baseEnd_3750732 < baseStart_3750732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750837 : List Nat := [1, 3, 3, 2, 1, 1, 1, 4, 2, 4]
def baseStart_3750837 : Nat := 118140960795 + 3750837 * 2 ^ 59
def prefixEnd_3750837 : Nat := 4983230072969 + 3 ^ 40 * 3750837 * 2
def baseEnd_3750837 : Nat := 1283988158445497711125147

theorem tailTrace_3750837 : CollatzResearch.WordTrace tailWord_3750837 prefixEnd_3750837 1283988158445497711125147 := by
  unfold tailWord_3750837
  simp only [CollatzResearch.WordTrace]
  refine ⟨136804264312365615804578765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91202842874910410536385843 136804264312365615804578765)
  ·
    refine ⟨51301599117137105926717037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136804264312365615804578765 51301599117137105926717037)
    ·
      refine ⟨19238099668926414722518889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51301599117137105926717037 19238099668926414722518889)
      ·
        refine ⟨14428574751694811041889167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19238099668926414722518889 14428574751694811041889167)
        ·
          refine ⟨21642862127542216562833751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14428574751694811041889167 21642862127542216562833751)
          ·
            refine ⟨32464293191313324844250627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21642862127542216562833751 32464293191313324844250627)
            ·
              refine ⟨48696439786969987266375941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32464293191313324844250627 48696439786969987266375941)
              ·
                refine ⟨9130582460056872612445489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48696439786969987266375941 9130582460056872612445489)
                ·
                  refine ⟨6847936845042654459334117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9130582460056872612445489 6847936845042654459334117)
                  ·
                    refine ⟨1283988158445497711125147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6847936845042654459334117 1283988158445497711125147)
                    ·
                      rfl

theorem cell22_3750837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_3750837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3750837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3750837 prefixEnd_3750837 := by exact prefixLift 3750837
  have htrace : WordTrace (prefixWord ++ tailWord_3750837) baseStart_3750837 baseEnd_3750837 := by
    simpa [prefixWord, tailWord_3750837, baseEnd_3750837] using wordTrace_append hprefix tailTrace_3750837
  have hstable : (prefixWord ++ tailWord_3750837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750837).length < 2 ^ (prefixWord ++ tailWord_3750837).sum := by decide
  have hdescent : baseEnd_3750837 < baseStart_3750837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750841 : List Nat := [1, 2, 1, 4, 2, 4, 2, 2, 4]
def baseStart_3750841 : Nat := 118140960795 + 3750841 * 2 ^ 59
def prefixEnd_3750841 : Nat := 4983230072969 + 3 ^ 40 * 3750841 * 2
def baseEnd_3750841 : Nat := 427996509242414344675045

theorem tailTrace_3750841 : CollatzResearch.WordTrace tailWord_3750841 prefixEnd_3750841 427996509242414344675045 := by
  unfold tailWord_3750841
  simp only [CollatzResearch.WordTrace]
  refine ⟨136804410204351124487724377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91202940136234082991816251 136804410204351124487724377)
  ·
    refine ⟨102603307653263343365793283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136804410204351124487724377 102603307653263343365793283)
    ·
      refine ⟨153904961479895015048689925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102603307653263343365793283 153904961479895015048689925)
      ·
        refine ⟨28857180277480315321629361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153904961479895015048689925 28857180277480315321629361)
        ·
          refine ⟨21642885208110236491222021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28857180277480315321629361 21642885208110236491222021)
          ·
            refine ⟨4058040976520669342104129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21642885208110236491222021 4058040976520669342104129)
            ·
              refine ⟨3043530732390502006578097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4058040976520669342104129 3043530732390502006578097)
              ·
                refine ⟨2282648049292876504933573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3043530732390502006578097 2282648049292876504933573)
                ·
                  refine ⟨427996509242414344675045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2282648049292876504933573 427996509242414344675045)
                  ·
                    rfl

theorem cell22_3750841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 2, 2, 4].length) (baseStart_3750841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3750841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3750841 prefixEnd_3750841 := by exact prefixLift 3750841
  have htrace : WordTrace (prefixWord ++ tailWord_3750841) baseStart_3750841 baseEnd_3750841 := by
    simpa [prefixWord, tailWord_3750841, baseEnd_3750841] using wordTrace_append hprefix tailTrace_3750841
  have hstable : (prefixWord ++ tailWord_3750841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750841).length < 2 ^ (prefixWord ++ tailWord_3750841).sum := by decide
  have hdescent : baseEnd_3750841 < baseStart_3750841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750865 : List Nat := [1, 2, 2, 1, 2, 1, 3, 2, 2, 6]
def baseStart_3750865 : Nat := 118140960795 + 3750865 * 2 ^ 59
def prefixEnd_3750865 : Nat := 4983230072969 + 3 ^ 40 * 3750865 * 2
def baseEnd_3750865 : Nat := 1283997743417714971425061

theorem tailTrace_3750865 : CollatzResearch.WordTrace tailWord_3750865 prefixEnd_3750865 1283997743417714971425061 := by
  unfold tailWord_3750865
  simp only [CollatzResearch.WordTrace]
  refine ⟨136805285556264176586598049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91203523704176117724398699 136805285556264176586598049)
  ·
    refine ⟨102603964167198132439948537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136805285556264176586598049 102603964167198132439948537)
    ·
      refine ⟨76952973125398599329961403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102603964167198132439948537 76952973125398599329961403)
      ·
        refine ⟨115429459688097898994942105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76952973125398599329961403 115429459688097898994942105)
        ·
          refine ⟨86572094766073424246206579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115429459688097898994942105 86572094766073424246206579)
          ·
            refine ⟨129858142149110136369309869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86572094766073424246206579 129858142149110136369309869)
            ·
              refine ⟨48696803305916301138491201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129858142149110136369309869 48696803305916301138491201)
              ·
                refine ⟨36522602479437225853868401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48696803305916301138491201 36522602479437225853868401)
                ·
                  refine ⟨27391951859577919390401301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36522602479437225853868401 27391951859577919390401301)
                  ·
                    refine ⟨1283997743417714971425061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27391951859577919390401301 1283997743417714971425061)
                    ·
                      rfl

theorem cell22_3750865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 6].length) (baseStart_3750865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3750865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3750865 prefixEnd_3750865 := by exact prefixLift 3750865
  have htrace : WordTrace (prefixWord ++ tailWord_3750865) baseStart_3750865 baseEnd_3750865 := by
    simpa [prefixWord, tailWord_3750865, baseEnd_3750865] using wordTrace_append hprefix tailTrace_3750865
  have hstable : (prefixWord ++ tailWord_3750865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750865).length < 2 ^ (prefixWord ++ tailWord_3750865).sum := by decide
  have hdescent : baseEnd_3750865 < baseStart_3750865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750869 : List Nat := [1, 3, 2, 3, 3, 1, 3, 6]
def baseStart_3750869 : Nat := 118140960795 + 3750869 * 2 ^ 59
def prefixEnd_3750869 : Nat := 4983230072969 + 3 ^ 40 * 3750869 * 2
def baseEnd_3750869 : Nat := 142666568077717810480561

theorem tailTrace_3750869 : CollatzResearch.WordTrace tailWord_3750869 prefixEnd_3750869 142666568077717810480561 := by
  unfold tailWord_3750869
  simp only [CollatzResearch.WordTrace]
  refine ⟨136805431448249685269743661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91203620965499790179829107 136805431448249685269743661)
  ·
    refine ⟨51302036793093631976153873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136805431448249685269743661 51302036793093631976153873)
    ·
      refine ⟨38476527594820223982115405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51302036793093631976153873 38476527594820223982115405)
      ·
        refine ⟨14428697848057583993293277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38476527594820223982115405 14428697848057583993293277)
        ·
          refine ⟨5410761693021593997484979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14428697848057583993293277 5410761693021593997484979)
          ·
            refine ⟨8116142539532390996227469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5410761693021593997484979 8116142539532390996227469)
            ·
              refine ⟨3043553452324646623585301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8116142539532390996227469 3043553452324646623585301)
              ·
                refine ⟨142666568077717810480561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3043553452324646623585301 142666568077717810480561)
                ·
                  rfl

theorem cell22_3750869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 3, 6].length) (baseStart_3750869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3750869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3750869 prefixEnd_3750869 := by exact prefixLift 3750869
  have htrace : WordTrace (prefixWord ++ tailWord_3750869) baseStart_3750869 baseEnd_3750869 := by
    simpa [prefixWord, tailWord_3750869, baseEnd_3750869] using wordTrace_append hprefix tailTrace_3750869
  have hstable : (prefixWord ++ tailWord_3750869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750869).length < 2 ^ (prefixWord ++ tailWord_3750869).sum := by decide
  have hdescent : baseEnd_3750869 < baseStart_3750869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750897 : List Nat := [1, 2, 2, 2, 4, 2, 1, 1, 7]
def baseStart_3750897 : Nat := 118140960795 + 3750897 * 2 ^ 59
def prefixEnd_3750897 : Nat := 4983230072969 + 3 ^ 40 * 3750897 * 2
def baseEnd_3750897 : Nat := 428002899223892518208321

theorem tailTrace_3750897 : CollatzResearch.WordTrace tailWord_3750897 prefixEnd_3750897 428002899223892518208321 := by
  unfold tailWord_3750897
  simp only [CollatzResearch.WordTrace]
  refine ⟨136806452692148246051762945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91204301794765497367841963 136806452692148246051762945)
  ·
    refine ⟨102604839519111184538822209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136806452692148246051762945 102604839519111184538822209)
    ·
      refine ⟨76953629639333388404116657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102604839519111184538822209 76953629639333388404116657)
      ·
        refine ⟨57715222229500041303087493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76953629639333388404116657 57715222229500041303087493)
        ·
          refine ⟨10821604168031257744328905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57715222229500041303087493 10821604168031257744328905)
          ·
            refine ⟨8116203126023443308246679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10821604168031257744328905 8116203126023443308246679)
            ·
              refine ⟨12174304689035164962370019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8116203126023443308246679 12174304689035164962370019)
              ·
                refine ⟨18261457033552747443555029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12174304689035164962370019 18261457033552747443555029)
                ·
                  refine ⟨428002899223892518208321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18261457033552747443555029 428002899223892518208321)
                  ·
                    rfl

theorem cell22_3750897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 7].length) (baseStart_3750897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3750897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3750897 prefixEnd_3750897 := by exact prefixLift 3750897
  have htrace : WordTrace (prefixWord ++ tailWord_3750897) baseStart_3750897 baseEnd_3750897 := by
    simpa [prefixWord, tailWord_3750897, baseEnd_3750897] using wordTrace_append hprefix tailTrace_3750897
  have hstable : (prefixWord ++ tailWord_3750897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750897).length < 2 ^ (prefixWord ++ tailWord_3750897).sum := by decide
  have hdescent : baseEnd_3750897 < baseStart_3750897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751010 : List Nat := [3, 3, 2, 2, 1, 3, 2, 2, 4]
def baseStart_3751010 : Nat := 118140960795 + 3751010 * 2 ^ 59
def prefixEnd_3751010 : Nat := 4983230072969 + 3 ^ 40 * 3751010 * 2
def baseEnd_3751010 : Nat := 428015793293660975516539

theorem tailTrace_3751010 : CollatzResearch.WordTrace tailWord_3751010 prefixEnd_3751010 428015793293660975516539 := by
  unfold tailWord_3751010
  simp only [CollatzResearch.WordTrace]
  refine ⟨34202643535184716587656621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91207049427159244233750989 34202643535184716587656621)
  ·
    refine ⟨12825991325694268720371233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34202643535184716587656621 12825991325694268720371233)
    ·
      refine ⟨9619493494270701540278425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12825991325694268720371233 9619493494270701540278425)
      ·
        refine ⟨7214620120703026155208819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9619493494270701540278425 7214620120703026155208819)
        ·
          refine ⟨10821930181054539232813229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7214620120703026155208819 10821930181054539232813229)
          ·
            refine ⟨4058223817895452212304961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10821930181054539232813229 4058223817895452212304961)
            ·
              refine ⟨3043667863421589159228721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4058223817895452212304961 3043667863421589159228721)
              ·
                refine ⟨2282750897566191869421541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3043667863421589159228721 2282750897566191869421541)
                ·
                  refine ⟨428015793293660975516539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2282750897566191869421541 428015793293660975516539)
                  ·
                    rfl

theorem cell22_3751010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 2, 2, 4].length) (baseStart_3751010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3751010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3751010 prefixEnd_3751010 := by exact prefixLift 3751010
  have htrace : WordTrace (prefixWord ++ tailWord_3751010) baseStart_3751010 baseEnd_3751010 := by
    simpa [prefixWord, tailWord_3751010, baseEnd_3751010] using wordTrace_append hprefix tailTrace_3751010
  have hstable : (prefixWord ++ tailWord_3751010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751010).length < 2 ^ (prefixWord ++ tailWord_3751010).sum := by decide
  have hdescent : baseEnd_3751010 < baseStart_3751010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751017 : List Nat := [1, 2, 1, 1, 1, 6, 1, 1, 2, 6]
def baseStart_3751017 : Nat := 118140960795 + 3751017 * 2 ^ 59
def prefixEnd_3751017 : Nat := 4983230072969 + 3 ^ 40 * 3751017 * 2
def baseEnd_3751017 : Nat := 1284049776124037241624595

theorem tailTrace_3751017 : CollatzResearch.WordTrace tailWord_3751017 prefixEnd_3751017 1284049776124037241624595 := by
  unfold tailWord_3751017
  simp only [CollatzResearch.WordTrace]
  refine ⟨136810829451713506546131305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91207219634475671030754203 136810829451713506546131305)
  ·
    refine ⟨102608122088785129909598479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136810829451713506546131305 102608122088785129909598479)
    ·
      refine ⟨153912183133177694864397719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102608122088785129909598479 153912183133177694864397719)
      ·
        refine ⟨230868274699766542296596579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153912183133177694864397719 230868274699766542296596579)
        ·
          refine ⟨346302412049649813444894869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230868274699766542296596579 346302412049649813444894869)
          ·
            refine ⟨16232925564827335005229447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 346302412049649813444894869 16232925564827335005229447)
            ·
              refine ⟨24349388347241002507844171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16232925564827335005229447 24349388347241002507844171)
              ·
                refine ⟨36524082520861503761766257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24349388347241002507844171 36524082520861503761766257)
                ·
                  refine ⟨27393061890646127821324693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36524082520861503761766257 27393061890646127821324693)
                  ·
                    refine ⟨1284049776124037241624595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27393061890646127821324693 1284049776124037241624595)
                    ·
                      rfl

theorem cell22_3751017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 6].length) (baseStart_3751017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3751017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3751017 prefixEnd_3751017 := by exact prefixLift 3751017
  have htrace : WordTrace (prefixWord ++ tailWord_3751017) baseStart_3751017 baseEnd_3751017 := by
    simpa [prefixWord, tailWord_3751017, baseEnd_3751017] using wordTrace_append hprefix tailTrace_3751017
  have hstable : (prefixWord ++ tailWord_3751017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751017).length < 2 ^ (prefixWord ++ tailWord_3751017).sum := by decide
  have hdescent : baseEnd_3751017 < baseStart_3751017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751047 : List Nat := [1, 1, 4, 2, 1, 1, 1, 1, 3, 7]
def baseStart_3751047 : Nat := 118140960795 + 3751047 * 2 ^ 59
def prefixEnd_3751047 : Nat := 4983230072969 + 3 ^ 40 * 3751047 * 2
def baseEnd_3751047 : Nat := 1284060045737127163374503

theorem tailTrace_3751047 : CollatzResearch.WordTrace tailWord_3751047 prefixEnd_3751047 1284060045737127163374503 := by
  unfold tailWord_3751047
  simp only [CollatzResearch.WordTrace]
  refine ⟨136811923641604821669723395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91207949094403214446482263 136811923641604821669723395)
  ·
    refine ⟨205217885462407232504585093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136811923641604821669723395 205217885462407232504585093)
    ·
      refine ⟨38478353524201356094609705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 205217885462407232504585093 38478353524201356094609705)
      ·
        refine ⟨28858765143151017070957279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38478353524201356094609705 28858765143151017070957279)
        ·
          refine ⟨43288147714726525606435919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28858765143151017070957279 43288147714726525606435919)
          ·
            refine ⟨64932221572089788409653879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43288147714726525606435919 64932221572089788409653879)
            ·
              refine ⟨97398332358134682614480819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64932221572089788409653879 97398332358134682614480819)
              ·
                refine ⟨146097498537202023921721229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97398332358134682614480819 146097498537202023921721229)
                ·
                  refine ⟨54786561951450758970645461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 146097498537202023921721229 54786561951450758970645461)
                  ·
                    refine ⟨1284060045737127163374503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54786561951450758970645461 1284060045737127163374503)
                    ·
                      rfl

theorem cell22_3751047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_3751047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3751047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3751047 prefixEnd_3751047 := by exact prefixLift 3751047
  have htrace : WordTrace (prefixWord ++ tailWord_3751047) baseStart_3751047 baseEnd_3751047 := by
    simpa [prefixWord, tailWord_3751047, baseEnd_3751047] using wordTrace_append hprefix tailTrace_3751047
  have hstable : (prefixWord ++ tailWord_3751047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751047).length < 2 ^ (prefixWord ++ tailWord_3751047).sum := by decide
  have hdescent : baseEnd_3751047 < baseStart_3751047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751064 : List Nat := [2, 1, 2, 4, 2, 1, 1, 2, 2, 5]
def baseStart_3751064 : Nat := 118140960795 + 3751064 * 2 ^ 59
def prefixEnd_3751064 : Nat := 4983230072969 + 3 ^ 40 * 3751064 * 2
def baseEnd_3751064 : Nat := 1284065865184544785699451

theorem tailTrace_3751064 : CollatzResearch.WordTrace tailWord_3751064 prefixEnd_3751064 1284065865184544785699451 := by
  unfold tailWord_3751064
  simp only [CollatzResearch.WordTrace]
  refine ⟨68406271841271616786546123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91208362455028822382061497 68406271841271616786546123)
  ·
    refine ⟨102609407761907425179819185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68406271841271616786546123 102609407761907425179819185)
    ·
      refine ⟨76957055821430568884864389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102609407761907425179819185 76957055821430568884864389)
      ·
        refine ⟨14429447966518231665912073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76957055821430568884864389 14429447966518231665912073)
        ·
          refine ⟨10822085974888673749434055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14429447966518231665912073 10822085974888673749434055)
          ·
            refine ⟨16233128962333010624151083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10822085974888673749434055 16233128962333010624151083)
            ·
              refine ⟨24349693443499515936226625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16233128962333010624151083 24349693443499515936226625)
              ·
                refine ⟨18262270082624636952169969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24349693443499515936226625 18262270082624636952169969)
                ·
                  refine ⟨13696702561968477714127477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18262270082624636952169969 13696702561968477714127477)
                  ·
                    refine ⟨1284065865184544785699451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13696702561968477714127477 1284065865184544785699451)
                    ·
                      rfl

theorem cell22_3751064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 2, 5].length) (baseStart_3751064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3751064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3751064 prefixEnd_3751064 := by exact prefixLift 3751064
  have htrace : WordTrace (prefixWord ++ tailWord_3751064) baseStart_3751064 baseEnd_3751064 := by
    simpa [prefixWord, tailWord_3751064, baseEnd_3751064] using wordTrace_append hprefix tailTrace_3751064
  have hstable : (prefixWord ++ tailWord_3751064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751064).length < 2 ^ (prefixWord ++ tailWord_3751064).sum := by decide
  have hdescent : baseEnd_3751064 < baseStart_3751064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751066 : List Nat := [3, 1, 1, 5, 1, 1, 3, 2, 5]
def baseStart_3751066 : Nat := 118140960795 + 3751066 * 2 ^ 59
def prefixEnd_3751066 : Nat := 4983230072969 + 3 ^ 40 * 3751066 * 2
def baseEnd_3751066 : Nat := 428022183275139149049815

theorem tailTrace_3751066 : CollatzResearch.WordTrace tailWord_3751066 prefixEnd_3751066 428022183275139149049815 := by
  unfold tailWord_3751066
  simp only [CollatzResearch.WordTrace]
  refine ⟨34203154157133996978666263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91208411085690658609776701 34203154157133996978666263)
  ·
    refine ⟨51304731235700995467999395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34203154157133996978666263 51304731235700995467999395)
    ·
      refine ⟨76957096853551493201999093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51304731235700995467999395 76957096853551493201999093)
      ·
        refine ⟨7214727830020452487687415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76957096853551493201999093 7214727830020452487687415)
        ·
          refine ⟨10822091745030678731531123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7214727830020452487687415 10822091745030678731531123)
          ·
            refine ⟨16233137617546018097296685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10822091745030678731531123 16233137617546018097296685)
            ·
              refine ⟨6087426606579756786486257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16233137617546018097296685 6087426606579756786486257)
              ·
                refine ⟨4565569954934817589864693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6087426606579756786486257 4565569954934817589864693)
                ·
                  refine ⟨428022183275139149049815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4565569954934817589864693 428022183275139149049815)
                  ·
                    rfl

theorem cell22_3751066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 2, 5].length) (baseStart_3751066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3751066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3751066 prefixEnd_3751066 := by exact prefixLift 3751066
  have htrace : WordTrace (prefixWord ++ tailWord_3751066) baseStart_3751066 baseEnd_3751066 := by
    simpa [prefixWord, tailWord_3751066, baseEnd_3751066] using wordTrace_append hprefix tailTrace_3751066
  have hstable : (prefixWord ++ tailWord_3751066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751066).length < 2 ^ (prefixWord ++ tailWord_3751066).sum := by decide
  have hdescent : baseEnd_3751066 < baseStart_3751066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751070 : List Nat := [4, 3, 1, 1, 2, 1, 2, 4, 1, 3]
def baseStart_3751070 : Nat := 118140960795 + 3751070 * 2 ^ 59
def prefixEnd_3751070 : Nat := 4983230072969 + 3 ^ 40 * 3751070 * 2
def baseEnd_3751070 : Nat := 1284067919107162770049433

theorem tailTrace_3751070 : CollatzResearch.WordTrace tailWord_3751070 prefixEnd_3751070 1284067919107162770049433 := by
  unfold tailWord_3751070
  simp only [CollatzResearch.WordTrace]
  refine ⟨17101595315065187074726333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91208508347014331065207109 17101595315065187074726333)
  ·
    refine ⟨6413098243149445153022375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17101595315065187074726333 6413098243149445153022375)
    ·
      refine ⟨9619647364724167729533563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6413098243149445153022375 9619647364724167729533563)
      ·
        refine ⟨14429471047086251594300345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9619647364724167729533563 14429471047086251594300345)
        ·
          refine ⟨10822103285314688695725259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14429471047086251594300345 10822103285314688695725259)
          ·
            refine ⟨16233154927972033043587889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10822103285314688695725259 16233154927972033043587889)
            ·
              refine ⟨12174866195979024782690917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16233154927972033043587889 12174866195979024782690917)
              ·
                refine ⟨2282787411746067146754547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12174866195979024782690917 2282787411746067146754547)
                ·
                  refine ⟨3424181117619100720131821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2282787411746067146754547 3424181117619100720131821)
                  ·
                    refine ⟨1284067919107162770049433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3424181117619100720131821 1284067919107162770049433)
                    ·
                      rfl

theorem cell22_3751070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_3751070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3751070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3751070 prefixEnd_3751070 := by exact prefixLift 3751070
  have htrace : WordTrace (prefixWord ++ tailWord_3751070) baseStart_3751070 baseEnd_3751070 := by
    simpa [prefixWord, tailWord_3751070, baseEnd_3751070] using wordTrace_append hprefix tailTrace_3751070
  have hstable : (prefixWord ++ tailWord_3751070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751070).length < 2 ^ (prefixWord ++ tailWord_3751070).sum := by decide
  have hdescent : baseEnd_3751070 < baseStart_3751070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751128 : List Nat := [2, 1, 2, 2, 6, 1, 1, 1, 6]
def baseStart_3751128 : Nat := 118140960795 + 3751128 * 2 ^ 59
def prefixEnd_3751128 : Nat := 4983230072969 + 3 ^ 40 * 3751128 * 2
def baseEnd_3751128 : Nat := 428029257897489984033085

theorem tailTrace_3751128 : CollatzResearch.WordTrace tailWord_3751128 prefixEnd_3751128 428029257897489984033085 := by
  unfold tailWord_3751128
  simp only [CollatzResearch.WordTrace]
  refine ⟨68407438977155686251711019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91209918636207581668948025 68407438977155686251711019)
  ·
    refine ⟨102611158465733529377566529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68407438977155686251711019 102611158465733529377566529)
    ·
      refine ⟨76958368849300147033174897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102611158465733529377566529 76958368849300147033174897)
      ·
        refine ⟨57718776636975110274881173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76958368849300147033174897 57718776636975110274881173)
        ·
          refine ⟨2705567654858208294135055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 57718776636975110274881173 2705567654858208294135055)
          ·
            refine ⟨4058351482287312441202583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2705567654858208294135055 4058351482287312441202583)
            ·
              refine ⟨6087527223430968661803875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4058351482287312441202583 6087527223430968661803875)
              ·
                refine ⟨9131290835146452992705813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6087527223430968661803875 9131290835146452992705813)
                ·
                  refine ⟨428029257897489984033085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9131290835146452992705813 428029257897489984033085)
                  ·
                    rfl

theorem cell22_3751128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 1, 6].length) (baseStart_3751128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3751128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3751128 prefixEnd_3751128 := by exact prefixLift 3751128
  have htrace : WordTrace (prefixWord ++ tailWord_3751128) baseStart_3751128 baseEnd_3751128 := by
    simpa [prefixWord, tailWord_3751128, baseEnd_3751128] using wordTrace_append hprefix tailTrace_3751128
  have hstable : (prefixWord ++ tailWord_3751128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751128).length < 2 ^ (prefixWord ++ tailWord_3751128).sum := by decide
  have hdescent : baseEnd_3751128 < baseStart_3751128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751246 : List Nat := [4, 1, 1, 1, 1, 1, 6, 1, 6]
def baseStart_3751246 : Nat := 118140960795 + 3751246 * 2 ^ 59
def prefixEnd_3751246 : Nat := 4983230072969 + 3 ^ 40 * 3751246 * 2
def baseEnd_3751246 : Nat := 428042722501318992549631

theorem tailTrace_3751246 : CollatzResearch.WordTrace tailWord_3751246 prefixEnd_3751246 428042722501318992549631 := by
  unfold tailWord_3751246
  simp only [CollatzResearch.WordTrace]
  refine ⟨17102397720985484832027199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91212787845255919104145061 17102397720985484832027199)
  ·
    refine ⟨25653596581478227248040799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17102397720985484832027199 25653596581478227248040799)
    ·
      refine ⟨38480394872217340872061199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25653596581478227248040799 38480394872217340872061199)
      ·
        refine ⟨57720592308326011308091799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38480394872217340872061199 57720592308326011308091799)
        ·
          refine ⟨86580888462489016962137699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57720592308326011308091799 86580888462489016962137699)
          ·
            refine ⟨129871332693733525443206549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86580888462489016962137699 129871332693733525443206549)
            ·
              refine ⟨6087718720018759005150307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 129871332693733525443206549 6087718720018759005150307)
              ·
                refine ⟨9131578080028138507725461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6087718720018759005150307 9131578080028138507725461)
                ·
                  refine ⟨428042722501318992549631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9131578080028138507725461 428042722501318992549631)
                  ·
                    rfl

theorem cell22_3751246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 1, 6].length) (baseStart_3751246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3751246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3751246 prefixEnd_3751246 := by exact prefixLift 3751246
  have htrace : WordTrace (prefixWord ++ tailWord_3751246) baseStart_3751246 baseEnd_3751246 := by
    simpa [prefixWord, tailWord_3751246, baseEnd_3751246] using wordTrace_append hprefix tailTrace_3751246
  have hstable : (prefixWord ++ tailWord_3751246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751246).length < 2 ^ (prefixWord ++ tailWord_3751246).sum := by decide
  have hdescent : baseEnd_3751246 < baseStart_3751246 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751276 : List Nat := [2, 2, 1, 1, 5, 1, 2, 1, 1, 6]
def baseStart_3751276 : Nat := 118140960795 + 3751276 * 2 ^ 59
def prefixEnd_3751276 : Nat := 4983230072969 + 3 ^ 40 * 3751276 * 2
def baseEnd_3751276 : Nat := 1284138437117046899398801

theorem tailTrace_3751276 : CollatzResearch.WordTrace tailWord_3751276 prefixEnd_3751276 1284138437117046899398801 := by
  unfold tailWord_3751276
  simp only [CollatzResearch.WordTrace]
  refine ⟨68410137978887596889904841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91213517305183462519873121 68410137978887596889904841)
  ·
    refine ⟨51307603484165697667428631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68410137978887596889904841 51307603484165697667428631)
    ·
      refine ⟨76961405226248546501142947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51307603484165697667428631 76961405226248546501142947)
      ·
        refine ⟨115442107839372819751714421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76961405226248546501142947 115442107839372819751714421)
        ·
          refine ⟨10822697609941201851723227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 115442107839372819751714421 10822697609941201851723227)
          ·
            refine ⟨16234046414911802777584841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10822697609941201851723227 16234046414911802777584841)
            ·
              refine ⟨12175534811183852083188631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16234046414911802777584841 12175534811183852083188631)
              ·
                refine ⟨18263302216775778124782947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12175534811183852083188631 18263302216775778124782947)
                ·
                  refine ⟨27394953325163667187174421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18263302216775778124782947 27394953325163667187174421)
                  ·
                    refine ⟨1284138437117046899398801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27394953325163667187174421 1284138437117046899398801)
                    ·
                      rfl

theorem cell22_3751276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 6].length) (baseStart_3751276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3751276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3751276 prefixEnd_3751276 := by exact prefixLift 3751276
  have htrace : WordTrace (prefixWord ++ tailWord_3751276) baseStart_3751276 baseEnd_3751276 := by
    simpa [prefixWord, tailWord_3751276, baseEnd_3751276] using wordTrace_append hprefix tailTrace_3751276
  have hstable : (prefixWord ++ tailWord_3751276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751276).length < 2 ^ (prefixWord ++ tailWord_3751276).sum := by decide
  have hdescent : baseEnd_3751276 < baseStart_3751276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751297 : List Nat := [1, 2, 4, 3, 2, 1, 3, 2, 4]
def baseStart_3751297 : Nat := 118140960795 + 3751297 * 2 ^ 59
def prefixEnd_3751297 : Nat := 4983230072969 + 3 ^ 40 * 3751297 * 2
def baseEnd_3751297 : Nat := 428048541948736614874579

theorem tailTrace_3751297 : CollatzResearch.WordTrace tailWord_3751297 prefixEnd_3751297 428048541948736614874579 := by
  unfold tailWord_3751297
  simp only [CollatzResearch.WordTrace]
  refine ⟨136821041890699114366324145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91214027927132742910882763 136821041890699114366324145)
  ·
    refine ⟨102615781418024335774743109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136821041890699114366324145 102615781418024335774743109)
    ·
      refine ⟨19240459015879562957764333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102615781418024335774743109 19240459015879562957764333)
      ·
        refine ⟨7215172130954836109161625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19240459015879562957764333 7215172130954836109161625)
        ·
          refine ⟨5411379098216127081871219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7215172130954836109161625 5411379098216127081871219)
          ·
            refine ⟨8117068647324190622806829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5411379098216127081871219 8117068647324190622806829)
            ·
              refine ⟨3043900742746571483552561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8117068647324190622806829 3043900742746571483552561)
              ·
                refine ⟨2282925557059928612664421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3043900742746571483552561 2282925557059928612664421)
                ·
                  refine ⟨428048541948736614874579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2282925557059928612664421 428048541948736614874579)
                  ·
                    rfl

theorem cell22_3751297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 3, 2, 4].length) (baseStart_3751297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3751297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3751297 prefixEnd_3751297 := by exact prefixLift 3751297
  have htrace : WordTrace (prefixWord ++ tailWord_3751297) baseStart_3751297 baseEnd_3751297 := by
    simpa [prefixWord, tailWord_3751297, baseEnd_3751297] using wordTrace_append hprefix tailTrace_3751297
  have hstable : (prefixWord ++ tailWord_3751297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751297).length < 2 ^ (prefixWord ++ tailWord_3751297).sum := by decide
  have hdescent : baseEnd_3751297 < baseStart_3751297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751351 : List Nat := [1, 1, 3, 1, 3, 2, 2, 2, 2, 5]
def baseStart_3751351 : Nat := 118140960795 + 3751351 * 2 ^ 59
def prefixEnd_3751351 : Nat := 4983230072969 + 3 ^ 40 * 3751351 * 2
def baseEnd_3751351 : Nat := 1284164111149771703773571

theorem tailTrace_3751351 : CollatzResearch.WordTrace tailWord_3751351 prefixEnd_3751351 1284164111149771703773571 := by
  unfold tailWord_3751351
  simp only [CollatzResearch.WordTrace]
  refine ⟨136823011432503481588789907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91215340955002321059193271 136823011432503481588789907)
  ·
    refine ⟨205234517148755222383184861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136823011432503481588789907 205234517148755222383184861)
    ·
      refine ⟨76962943930783208393694323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205234517148755222383184861 76962943930783208393694323)
      ·
        refine ⟨115444415896174812590541485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76962943930783208393694323 115444415896174812590541485)
        ·
          refine ⟨43291655961065554721453057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115444415896174812590541485 43291655961065554721453057)
          ·
            refine ⟨32468741970799166041089793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43291655961065554721453057 32468741970799166041089793)
            ·
              refine ⟨24351556478099374530817345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32468741970799166041089793 24351556478099374530817345)
              ·
                refine ⟨18263667358574530898113009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24351556478099374530817345 18263667358574530898113009)
                ·
                  refine ⟨13697750518930898173584757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18263667358574530898113009 13697750518930898173584757)
                  ·
                    refine ⟨1284164111149771703773571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13697750518930898173584757 1284164111149771703773571)
                    ·
                      rfl

theorem cell22_3751351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 2, 5].length) (baseStart_3751351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3751351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3751351 prefixEnd_3751351 := by exact prefixLift 3751351
  have htrace : WordTrace (prefixWord ++ tailWord_3751351) baseStart_3751351 baseEnd_3751351 := by
    simpa [prefixWord, tailWord_3751351, baseEnd_3751351] using wordTrace_append hprefix tailTrace_3751351
  have hstable : (prefixWord ++ tailWord_3751351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751351).length < 2 ^ (prefixWord ++ tailWord_3751351).sum := by decide
  have hdescent : baseEnd_3751351 < baseStart_3751351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751441 : List Nat := [1, 2, 2, 1, 1, 2, 3, 1, 2, 7]
def baseStart_3751441 : Nat := 118140960795 + 3751441 * 2 ^ 59
def prefixEnd_3751441 : Nat := 4983230072969 + 3 ^ 40 * 3751441 * 2
def baseEnd_3751441 : Nat := 1284194919989041469023295

theorem tailTrace_3751441 : CollatzResearch.WordTrace tailWord_3751441 prefixEnd_3751441 1284194919989041469023295 := by
  unfold tailWord_3751441
  simp only [CollatzResearch.WordTrace]
  refine ⟨136826294002177426959566177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91217529334784951306377451 136826294002177426959566177)
  ·
    refine ⟨102619720501633070219674633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136826294002177426959566177 102619720501633070219674633)
    ·
      refine ⟨76964790376224802664755975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102619720501633070219674633 76964790376224802664755975)
      ·
        refine ⟨115447185564337203997133963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76964790376224802664755975 115447185564337203997133963)
        ·
          refine ⟨173170778346505805995700945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115447185564337203997133963 173170778346505805995700945)
          ·
            refine ⟨129878083759879354496775709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173170778346505805995700945 129878083759879354496775709)
            ·
              refine ⟨48704281409954757936290891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129878083759879354496775709 48704281409954757936290891)
              ·
                refine ⟨73056422114932136904436337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48704281409954757936290891 73056422114932136904436337)
                ·
                  refine ⟨54792316586199102678327253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73056422114932136904436337 54792316586199102678327253)
                  ·
                    refine ⟨1284194919989041469023295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54792316586199102678327253 1284194919989041469023295)
                    ·
                      rfl

theorem cell22_3751441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 7].length) (baseStart_3751441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3751441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3751441 prefixEnd_3751441 := by exact prefixLift 3751441
  have htrace : WordTrace (prefixWord ++ tailWord_3751441) baseStart_3751441 baseEnd_3751441 := by
    simpa [prefixWord, tailWord_3751441, baseEnd_3751441] using wordTrace_append hprefix tailTrace_3751441
  have hstable : (prefixWord ++ tailWord_3751441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751441).length < 2 ^ (prefixWord ++ tailWord_3751441).sum := by decide
  have hdescent : baseEnd_3751441 < baseStart_3751441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751443 : List Nat := [1, 1, 1, 2, 1, 6, 4, 6]
def baseStart_3751443 : Nat := 118140960795 + 3751443 * 2 ^ 59
def prefixEnd_3751443 : Nat := 4983230072969 + 3 ^ 40 * 3751443 * 2
def baseEnd_3751443 : Nat := 142688400514434903385921

theorem tailTrace_3751443 : CollatzResearch.WordTrace tailWord_3751443 prefixEnd_3751443 142688400514434903385921 := by
  unfold tailWord_3751443
  simp only [CollatzResearch.WordTrace]
  refine ⟨136826366948170181301138983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91217577965446787534092655 136826366948170181301138983)
  ·
    refine ⟨205239550422255271951708475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136826366948170181301138983 205239550422255271951708475)
    ·
      refine ⟨307859325633382907927562713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205239550422255271951708475 307859325633382907927562713)
      ·
        refine ⟨230894494225037180945672035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307859325633382907927562713 230894494225037180945672035)
        ·
          refine ⟨346341741337555771418508053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230894494225037180945672035 346341741337555771418508053)
          ·
            refine ⟨16234769125197926785242565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 346341741337555771418508053 16234769125197926785242565)
            ·
              refine ⟨3044019210974611272232981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16234769125197926785242565 3044019210974611272232981)
              ·
                refine ⟨142688400514434903385921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3044019210974611272232981 142688400514434903385921)
                ·
                  rfl

theorem cell22_3751443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 4, 6].length) (baseStart_3751443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3751443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3751443 prefixEnd_3751443 := by exact prefixLift 3751443
  have htrace : WordTrace (prefixWord ++ tailWord_3751443) baseStart_3751443 baseEnd_3751443 := by
    simpa [prefixWord, tailWord_3751443, baseEnd_3751443] using wordTrace_append hprefix tailTrace_3751443
  have hstable : (prefixWord ++ tailWord_3751443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751443).length < 2 ^ (prefixWord ++ tailWord_3751443).sum := by decide
  have hdescent : baseEnd_3751443 < baseStart_3751443 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751475 : List Nat := [1, 1, 1, 2, 4, 3, 3, 1, 3, 3]
def baseStart_3751475 : Nat := 118140960795 + 3751475 * 2 ^ 59
def prefixEnd_3751475 : Nat := 4983230072969 + 3 ^ 40 * 3751475 * 2
def baseEnd_3751475 : Nat := 1284206558883876713673191

theorem tailTrace_3751475 : CollatzResearch.WordTrace tailWord_3751475 prefixEnd_3751475 1284206558883876713673191 := by
  unfold tailWord_3751475
  simp only [CollatzResearch.WordTrace]
  refine ⟨136827534084054250766303879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91218356056036167177535919 136827534084054250766303879)
  ·
    refine ⟨205241301126081376149455819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136827534084054250766303879 205241301126081376149455819)
    ·
      refine ⟨307861951689122064224183729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205241301126081376149455819 307861951689122064224183729)
      ·
        refine ⟨230896463766841548168137797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307861951689122064224183729 230896463766841548168137797)
        ·
          refine ⟨43293086956282790281525837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 230896463766841548168137797 43293086956282790281525837)
          ·
            refine ⟨16234907608606046355572189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43293086956282790281525837 16234907608606046355572189)
            ·
              refine ⟨6088090353227267383339571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16234907608606046355572189 6088090353227267383339571)
              ·
                refine ⟨9132135529840901075009357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6088090353227267383339571 9132135529840901075009357)
                ·
                  refine ⟨3424550823690337903128509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9132135529840901075009357 3424550823690337903128509)
                  ·
                    refine ⟨1284206558883876713673191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3424550823690337903128509 1284206558883876713673191)
                    ·
                      rfl

theorem cell22_3751475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 1, 3, 3].length) (baseStart_3751475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3751475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3751475 prefixEnd_3751475 := by exact prefixLift 3751475
  have htrace : WordTrace (prefixWord ++ tailWord_3751475) baseStart_3751475 baseEnd_3751475 := by
    simpa [prefixWord, tailWord_3751475, baseEnd_3751475] using wordTrace_append hprefix tailTrace_3751475
  have hstable : (prefixWord ++ tailWord_3751475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751475).length < 2 ^ (prefixWord ++ tailWord_3751475).sum := by decide
  have hdescent : baseEnd_3751475 < baseStart_3751475 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751563 : List Nat := [1, 1, 1, 1, 4, 1, 5, 1, 1, 6]
def baseStart_3751563 : Nat := 118140960795 + 3751563 * 2 ^ 59
def prefixEnd_3751563 : Nat := 4983230072969 + 3 ^ 40 * 3751563 * 2
def baseEnd_3751563 : Nat := 1284236683082273817472921

theorem tailTrace_3751563 : CollatzResearch.WordTrace tailWord_3751563 prefixEnd_3751563 1284236683082273817472921 := by
  unfold tailWord_3751563
  simp only [CollatzResearch.WordTrace]
  refine ⟨136830743707735441795507343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91220495805156961197004895 136830743707735441795507343)
  ·
    refine ⟨205246115561603162693261015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136830743707735441795507343 205246115561603162693261015)
    ·
      refine ⟨307869173342404744039891523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205246115561603162693261015 307869173342404744039891523)
      ·
        refine ⟨461803760013607116059837285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307869173342404744039891523 461803760013607116059837285)
        ·
          refine ⟨86588205002551334261219491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 461803760013607116059837285 86588205002551334261219491)
          ·
            refine ⟨129882307503827001391829237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86588205002551334261219491 129882307503827001391829237)
            ·
              refine ⟨12176466328483781380483991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 129882307503827001391829237 12176466328483781380483991)
              ·
                refine ⟨18264699492725672070725987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12176466328483781380483991 18264699492725672070725987)
                ·
                  refine ⟨27397049239088508106088981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18264699492725672070725987 27397049239088508106088981)
                  ·
                    refine ⟨1284236683082273817472921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27397049239088508106088981 1284236683082273817472921)
                    ·
                      rfl

theorem cell22_3751563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 6].length) (baseStart_3751563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3751563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3751563 prefixEnd_3751563 := by exact prefixLift 3751563
  have htrace : WordTrace (prefixWord ++ tailWord_3751563) baseStart_3751563 baseEnd_3751563 := by
    simpa [prefixWord, tailWord_3751563, baseEnd_3751563] using wordTrace_append hprefix tailTrace_3751563
  have hstable : (prefixWord ++ tailWord_3751563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751563).length < 2 ^ (prefixWord ++ tailWord_3751563).sum := by decide
  have hdescent : baseEnd_3751563 < baseStart_3751563 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751608 : List Nat := [2, 1, 2, 1, 2, 1, 1, 4, 2, 6]
def baseStart_3751608 : Nat := 118140960795 + 3751608 * 2 ^ 59
def prefixEnd_3751608 : Nat := 4983230072969 + 3 ^ 40 * 3751608 * 2
def baseEnd_3751608 : Nat := 1284252087501908700097783

theorem tailTrace_3751608 : CollatzResearch.WordTrace tailWord_3751608 prefixEnd_3751608 1284252087501908700097783 := by
  unfold tailWord_3751608
  simp only [CollatzResearch.WordTrace]
  refine ⟨68416192496286207240447739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91221589995048276320596985 68416192496286207240447739)
  ·
    refine ⟨102624288744429310860671609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68416192496286207240447739 102624288744429310860671609)
    ·
      refine ⟨76968216558321983145503707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102624288744429310860671609 76968216558321983145503707)
      ·
        refine ⟨115452324837482974718255561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76968216558321983145503707 115452324837482974718255561)
        ·
          refine ⟨86589243628112231038691671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115452324837482974718255561 86589243628112231038691671)
          ·
            refine ⟨129883865442168346558037507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86589243628112231038691671 129883865442168346558037507)
            ·
              refine ⟨194825798163252519837056261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129883865442168346558037507 194825798163252519837056261)
              ·
                refine ⟨36529837155609847469448049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 194825798163252519837056261 36529837155609847469448049)
                ·
                  refine ⟨27397377866707385602086037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36529837155609847469448049 27397377866707385602086037)
                  ·
                    refine ⟨1284252087501908700097783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27397377866707385602086037 1284252087501908700097783)
                    ·
                      rfl

theorem cell22_3751608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 2, 6].length) (baseStart_3751608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3751608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3751608 prefixEnd_3751608 := by exact prefixLift 3751608
  have htrace : WordTrace (prefixWord ++ tailWord_3751608) baseStart_3751608 baseEnd_3751608 := by
    simpa [prefixWord, tailWord_3751608, baseEnd_3751608] using wordTrace_append hprefix tailTrace_3751608
  have hstable : (prefixWord ++ tailWord_3751608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751608).length < 2 ^ (prefixWord ++ tailWord_3751608).sum := by decide
  have hdescent : baseEnd_3751608 < baseStart_3751608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751612 : List Nat := [2, 2, 2, 3, 1, 4, 2, 6]
def baseStart_3751612 : Nat := 118140960795 + 3751612 * 2 ^ 59
def prefixEnd_3751612 : Nat := 4983230072969 + 3 ^ 40 * 3751612 * 2
def baseEnd_3751612 : Nat := 142694828531517113666419

theorem tailTrace_3751612 : CollatzResearch.WordTrace tailWord_3751612 prefixEnd_3751612 142694828531517113666419 := by
  unfold tailWord_3751612
  simp only [CollatzResearch.WordTrace]
  refine ⟨68416265442278961582020545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91221687256371948776027393 68416265442278961582020545)
  ·
    refine ⟨51312199081709221186515409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68416265442278961582020545 51312199081709221186515409)
    ·
      refine ⟨38484149311281915889886557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51312199081709221186515409 38484149311281915889886557)
      ·
        refine ⟨14431555991730718458707459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38484149311281915889886557 14431555991730718458707459)
        ·
          refine ⟨21647333987596077688061189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14431555991730718458707459 21647333987596077688061189)
          ·
            refine ⟨4058875122674264566511473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21647333987596077688061189 4058875122674264566511473)
            ·
              refine ⟨3044156342005698424883605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4058875122674264566511473 3044156342005698424883605)
              ·
                refine ⟨142694828531517113666419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3044156342005698424883605 142694828531517113666419)
                ·
                  rfl

theorem cell22_3751612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 2, 6].length) (baseStart_3751612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3751612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3751612 prefixEnd_3751612 := by exact prefixLift 3751612
  have htrace : WordTrace (prefixWord ++ tailWord_3751612) baseStart_3751612 baseEnd_3751612 := by
    simpa [prefixWord, tailWord_3751612, baseEnd_3751612] using wordTrace_append hprefix tailTrace_3751612
  have hstable : (prefixWord ++ tailWord_3751612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751612).length < 2 ^ (prefixWord ++ tailWord_3751612).sum := by decide
  have hdescent : baseEnd_3751612 < baseStart_3751612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751623 : List Nat := [1, 1, 4, 1, 1, 1, 3, 1, 9]
def baseStart_3751623 : Nat := 118140960795 + 3751623 * 2 ^ 59
def prefixEnd_3751623 : Nat := 4983230072969 + 3 ^ 40 * 3751623 * 2
def baseEnd_3751623 : Nat := 428085740769484553657579

theorem tailTrace_3751623 : CollatzResearch.WordTrace tailWord_3751623 prefixEnd_3751623 428085740769484553657579 := by
  unfold tailWord_3751623
  simp only [CollatzResearch.WordTrace]
  refine ⟨136832932087518072042691523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91221954725012048028461015 136832932087518072042691523)
  ·
    refine ⟨205249398131277108064037285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136832932087518072042691523 205249398131277108064037285)
    ·
      refine ⟨38484262149614457762006991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 205249398131277108064037285 38484262149614457762006991)
      ·
        refine ⟨57726393224421686643010487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38484262149614457762006991 57726393224421686643010487)
        ·
          refine ⟨86589589836632529964515731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57726393224421686643010487 86589589836632529964515731)
          ·
            refine ⟨129884384754948794946773597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86589589836632529964515731 129884384754948794946773597)
            ·
              refine ⟨48706644283105798105040099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129884384754948794946773597 48706644283105798105040099)
              ·
                refine ⟨73059966424658697157560149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48706644283105798105040099 73059966424658697157560149)
                ·
                  refine ⟨428085740769484553657579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 73059966424658697157560149 428085740769484553657579)
                  ·
                    rfl

theorem cell22_3751623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 9].length) (baseStart_3751623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3751623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3751623 prefixEnd_3751623 := by exact prefixLift 3751623
  have htrace : WordTrace (prefixWord ++ tailWord_3751623) baseStart_3751623 baseEnd_3751623 := by
    simpa [prefixWord, tailWord_3751623, baseEnd_3751623] using wordTrace_append hprefix tailTrace_3751623
  have hstable : (prefixWord ++ tailWord_3751623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751623).length < 2 ^ (prefixWord ++ tailWord_3751623).sum := by decide
  have hdescent : baseEnd_3751623 < baseStart_3751623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751640 : List Nat := [2, 1, 2, 2, 3, 1, 2, 4, 5]
def baseStart_3751640 : Nat := 118140960795 + 3751640 * 2 ^ 59
def prefixEnd_3751640 : Nat := 4983230072969 + 3 ^ 40 * 3751640 * 2
def baseEnd_3751640 : Nat := 428087680585290427765895

theorem tailTrace_3751640 : CollatzResearch.WordTrace tailWord_3751640 prefixEnd_3751640 428087680585290427765895 := by
  unfold tailWord_3751640
  simp only [CollatzResearch.WordTrace]
  refine ⟨68416776064228241973030187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91222368085637655964040249 68416776064228241973030187)
  ·
    refine ⟨102625164096342362959545281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68416776064228241973030187 102625164096342362959545281)
    ·
      refine ⟨76968873072256772219658961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102625164096342362959545281 76968873072256772219658961)
      ·
        refine ⟨57726654804192579164744221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76968873072256772219658961 57726654804192579164744221)
        ·
          refine ⟨21647495551572217186779083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57726654804192579164744221 21647495551572217186779083)
          ·
            refine ⟨32471243327358325780168625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21647495551572217186779083 32471243327358325780168625)
            ·
              refine ⟨24353432495518744335126469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32471243327358325780168625 24353432495518744335126469)
              ·
                refine ⟨4566268592909764562836213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24353432495518744335126469 4566268592909764562836213)
                ·
                  refine ⟨428087680585290427765895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4566268592909764562836213 428087680585290427765895)
                  ·
                    rfl

theorem cell22_3751640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 4, 5].length) (baseStart_3751640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3751640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3751640 prefixEnd_3751640 := by exact prefixLift 3751640
  have htrace : WordTrace (prefixWord ++ tailWord_3751640) baseStart_3751640 baseEnd_3751640 := by
    simpa [prefixWord, tailWord_3751640, baseEnd_3751640] using wordTrace_append hprefix tailTrace_3751640
  have hstable : (prefixWord ++ tailWord_3751640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751640).length < 2 ^ (prefixWord ++ tailWord_3751640).sum := by decide
  have hdescent : baseEnd_3751640 < baseStart_3751640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751715 : List Nat := [1, 1, 1, 4, 2, 1, 2, 2, 4, 4]
def baseStart_3751715 : Nat := 118140960795 + 3751715 * 2 ^ 59
def prefixEnd_3751715 : Nat := 4983230072969 + 3 ^ 40 * 3751715 * 2
def baseEnd_3751715 : Nat := 1284288715788596087672455

theorem tailTrace_3751715 : CollatzResearch.WordTrace tailWord_3751715 prefixEnd_3751715 1284288715788596087672455 := by
  unfold tailWord_3751715
  simp only [CollatzResearch.WordTrace]
  refine ⟨136836287603184771755040599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91224191735456514503360399 136836287603184771755040599)
  ·
    refine ⟨205254431404777157632560899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136836287603184771755040599 205254431404777157632560899)
    ·
      refine ⟨307881647107165736448841349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205254431404777157632560899 307881647107165736448841349)
      ·
        refine ⟨57727808832593575584157753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 307881647107165736448841349 57727808832593575584157753)
        ·
          refine ⟨43295856624445181688118315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57727808832593575584157753 43295856624445181688118315)
          ·
            refine ⟨64943784936667772532177473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43295856624445181688118315 64943784936667772532177473)
            ·
              refine ⟨48707838702500829399133105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64943784936667772532177473 48707838702500829399133105)
              ·
                refine ⟨36530879026875622049349829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48707838702500829399133105 36530879026875622049349829)
                ·
                  refine ⟨6849539817539179134253093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36530879026875622049349829 6849539817539179134253093)
                  ·
                    refine ⟨1284288715788596087672455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6849539817539179134253093 1284288715788596087672455)
                    ·
                      rfl

theorem cell22_3751715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 4, 4].length) (baseStart_3751715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3751715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3751715 prefixEnd_3751715 := by exact prefixLift 3751715
  have htrace : WordTrace (prefixWord ++ tailWord_3751715) baseStart_3751715 baseEnd_3751715 := by
    simpa [prefixWord, tailWord_3751715, baseEnd_3751715] using wordTrace_append hprefix tailTrace_3751715
  have hstable : (prefixWord ++ tailWord_3751715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751715).length < 2 ^ (prefixWord ++ tailWord_3751715).sum := by decide
  have hdescent : baseEnd_3751715 < baseStart_3751715 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751717 : List Nat := [1, 3, 1, 2, 3, 3, 2, 1, 1, 5]
def baseStart_3751717 : Nat := 118140960795 + 3751717 * 2 ^ 59
def prefixEnd_3751717 : Nat := 4983230072969 + 3 ^ 40 * 3751717 * 2
def baseEnd_3751717 : Nat := 1284289400429468749122449

theorem tailTrace_3751717 : CollatzResearch.WordTrace tailWord_3751717 prefixEnd_3751717 1284289400429468749122449 := by
  unfold tailWord_3751717
  simp only [CollatzResearch.WordTrace]
  refine ⟨136836360549177526096613405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91224240366118350731075603 136836360549177526096613405)
  ·
    refine ⟨51313635205941572286230027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136836360549177526096613405 51313635205941572286230027)
    ·
      refine ⟨76970452808912358429345041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51313635205941572286230027 76970452808912358429345041)
      ·
        refine ⟨57727839606684268822008781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76970452808912358429345041 57727839606684268822008781)
        ·
          refine ⟨21647939852506600808253293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57727839606684268822008781 21647939852506600808253293)
          ·
            refine ⟨8117977444689975303094985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21647939852506600808253293 8117977444689975303094985)
            ·
              refine ⟨6088483083517481477321239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8117977444689975303094985 6088483083517481477321239)
              ·
                refine ⟨9132724625276222215981859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6088483083517481477321239 9132724625276222215981859)
                ·
                  refine ⟨13699086937914333323972789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9132724625276222215981859 13699086937914333323972789)
                  ·
                    refine ⟨1284289400429468749122449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13699086937914333323972789 1284289400429468749122449)
                    ·
                      rfl

theorem cell22_3751717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 1, 1, 5].length) (baseStart_3751717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3751717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3751717 prefixEnd_3751717 := by exact prefixLift 3751717
  have htrace : WordTrace (prefixWord ++ tailWord_3751717) baseStart_3751717 baseEnd_3751717 := by
    simpa [prefixWord, tailWord_3751717, baseEnd_3751717] using wordTrace_append hprefix tailTrace_3751717
  have hstable : (prefixWord ++ tailWord_3751717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751717).length < 2 ^ (prefixWord ++ tailWord_3751717).sum := by decide
  have hdescent : baseEnd_3751717 < baseStart_3751717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751734 : List Nat := [5, 1, 2, 2, 1, 1, 2, 2, 1, 5]
def baseStart_3751734 : Nat := 118140960795 + 3751734 * 2 ^ 59
def prefixEnd_3751734 : Nat := 4983230072969 + 3 ^ 40 * 3751734 * 2
def baseEnd_3751734 : Nat := 1284295219876886371447397

theorem tailTrace_3751734 : CollatzResearch.WordTrace tailWord_3751734 prefixEnd_3751734 1284295219876886371447397 := by
  unfold tailWord_3751734
  simp only [CollatzResearch.WordTrace]
  refine ⟨8552311286882246124998891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91224653726743958666654837 8552311286882246124998891)
  ·
    refine ⟨12828466930323369187498337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8552311286882246124998891 12828466930323369187498337)
    ·
      refine ⟨9621350197742526890623753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12828466930323369187498337 9621350197742526890623753)
      ·
        refine ⟨7216012648306895167967815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9621350197742526890623753 7216012648306895167967815)
        ·
          refine ⟨10824018972460342751951723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7216012648306895167967815 10824018972460342751951723)
          ·
            refine ⟨16236028458690514127927585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10824018972460342751951723 16236028458690514127927585)
            ·
              refine ⟨12177021344017885595945689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16236028458690514127927585 12177021344017885595945689)
              ·
                refine ⟨9132766008013414196959267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12177021344017885595945689 9132766008013414196959267)
                ·
                  refine ⟨13699149012020121295438901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9132766008013414196959267 13699149012020121295438901)
                  ·
                    refine ⟨1284295219876886371447397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13699149012020121295438901 1284295219876886371447397)
                    ·
                      rfl

theorem cell22_3751734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_3751734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3751734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3751734 prefixEnd_3751734 := by exact prefixLift 3751734
  have htrace : WordTrace (prefixWord ++ tailWord_3751734) baseStart_3751734 baseEnd_3751734 := by
    simpa [prefixWord, tailWord_3751734, baseEnd_3751734] using wordTrace_append hprefix tailTrace_3751734
  have hstable : (prefixWord ++ tailWord_3751734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751734).length < 2 ^ (prefixWord ++ tailWord_3751734).sum := by decide
  have hdescent : baseEnd_3751734 < baseStart_3751734 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751826 : List Nat := [3, 2, 3, 2, 1, 1, 4, 1, 5]
def baseStart_3751826 : Nat := 118140960795 + 3751826 * 2 ^ 59
def prefixEnd_3751826 : Nat := 4983230072969 + 3 ^ 40 * 3751826 * 2
def baseEnd_3751826 : Nat := 428108904452342932715705

theorem tailTrace_3751826 : CollatzResearch.WordTrace tailWord_3751826 prefixEnd_3751826 428108904452342932715705 := by
  unfold tailWord_3751826
  simp only [CollatzResearch.WordTrace]
  refine ⟨34210084026445659428082833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91226890737188425141554221 34210084026445659428082833)
  ·
    refine ⟨25657563019834244571062125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34210084026445659428082833 25657563019834244571062125)
    ·
      refine ⟨9621586132437841714148297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25657563019834244571062125 9621586132437841714148297)
      ·
        refine ⟨7216189599328381285611223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9621586132437841714148297 7216189599328381285611223)
        ·
          refine ⟨10824284398992571928416835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7216189599328381285611223 10824284398992571928416835)
          ·
            refine ⟨16236426598488857892625253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10824284398992571928416835 16236426598488857892625253)
            ·
              refine ⟨3044329987216660854867235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16236426598488857892625253 3044329987216660854867235)
              ·
                refine ⟨4566494980824991282300853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3044329987216660854867235 4566494980824991282300853)
                ·
                  refine ⟨428108904452342932715705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4566494980824991282300853 428108904452342932715705)
                  ·
                    rfl

theorem cell22_3751826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 4, 1, 5].length) (baseStart_3751826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3751826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3751826 prefixEnd_3751826 := by exact prefixLift 3751826
  have htrace : WordTrace (prefixWord ++ tailWord_3751826) baseStart_3751826 baseEnd_3751826 := by
    simpa [prefixWord, tailWord_3751826, baseEnd_3751826] using wordTrace_append hprefix tailTrace_3751826
  have hstable : (prefixWord ++ tailWord_3751826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751826).length < 2 ^ (prefixWord ++ tailWord_3751826).sum := by decide
  have hdescent : baseEnd_3751826 < baseStart_3751826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751839 : List Nat := [1, 1, 2, 5, 3, 1, 1, 1, 3, 4]
def baseStart_3751839 : Nat := 118140960795 + 3751839 * 2 ^ 59
def prefixEnd_3751839 : Nat := 4983230072969 + 3 ^ 40 * 3751839 * 2
def baseEnd_3751839 : Nat := 1284331163522701097572075

theorem tailTrace_3751839 : CollatzResearch.WordTrace tailWord_3751839 prefixEnd_3751839 1284331163522701097572075 := by
  unfold tailWord_3751839
  simp only [CollatzResearch.WordTrace]
  refine ⟨136840810254735540932554571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91227206836490360621703047 136840810254735540932554571)
  ·
    refine ⟨205261215382103311398831857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136840810254735540932554571 205261215382103311398831857)
    ·
      refine ⟨153945911536577483549123893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205261215382103311398831857 153945911536577483549123893)
      ·
        refine ⟨14432429206554139082730365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 153945911536577483549123893 14432429206554139082730365)
        ·
          refine ⟨5412160952457802156023887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14432429206554139082730365 5412160952457802156023887)
          ·
            refine ⟨8118241428686703234035831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5412160952457802156023887 8118241428686703234035831)
            ·
              refine ⟨12177362143030054851053747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8118241428686703234035831 12177362143030054851053747)
              ·
                refine ⟨18266043214545082276580621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12177362143030054851053747 18266043214545082276580621)
                ·
                  refine ⟨6849766205454405853717733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18266043214545082276580621 6849766205454405853717733)
                  ·
                    refine ⟨1284331163522701097572075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6849766205454405853717733 1284331163522701097572075)
                    ·
                      rfl

theorem cell22_3751839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 3, 4].length) (baseStart_3751839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3751839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3751839 prefixEnd_3751839 := by exact prefixLift 3751839
  have htrace : WordTrace (prefixWord ++ tailWord_3751839) baseStart_3751839 baseEnd_3751839 := by
    simpa [prefixWord, tailWord_3751839, baseEnd_3751839] using wordTrace_append hprefix tailTrace_3751839
  have hstable : (prefixWord ++ tailWord_3751839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751839).length < 2 ^ (prefixWord ++ tailWord_3751839).sum := by decide
  have hdescent : baseEnd_3751839 < baseStart_3751839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751882 : List Nat := [3, 1, 2, 1, 2, 1, 5, 7]
def baseStart_3751882 : Nat := 118140960795 + 3751882 * 2 ^ 59
def prefixEnd_3751882 : Nat := 4983230072969 + 3 ^ 40 * 3751882 * 2
def baseEnd_3751882 : Nat := 142705098144607035416327

theorem tailTrace_3751882 : CollatzResearch.WordTrace tailWord_3751882 prefixEnd_3751882 142705098144607035416327 := by
  unfold tailWord_3751882
  simp only [CollatzResearch.WordTrace]
  refine ⟨34210594648394939819092475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91228252395719839517579933 34210594648394939819092475)
  ·
    refine ⟨51315891972592409728638713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34210594648394939819092475 51315891972592409728638713)
    ·
      refine ⟨38486918979444307296479035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51315891972592409728638713 38486918979444307296479035)
      ·
        refine ⟨57730378469166460944718553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38486918979444307296479035 57730378469166460944718553)
        ·
          refine ⟨43297783851874845708538915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57730378469166460944718553 43297783851874845708538915)
          ·
            refine ⟨64946675777812268562808373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43297783851874845708538915 64946675777812268562808373)
            ·
              refine ⟨6088750854169900177763285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64946675777812268562808373 6088750854169900177763285)
              ·
                refine ⟨142705098144607035416327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6088750854169900177763285 142705098144607035416327)
                ·
                  rfl

theorem cell22_3751882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 7].length) (baseStart_3751882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3751882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3751882 prefixEnd_3751882 := by exact prefixLift 3751882
  have htrace : WordTrace (prefixWord ++ tailWord_3751882) baseStart_3751882 baseEnd_3751882 := by
    simpa [prefixWord, tailWord_3751882, baseEnd_3751882] using wordTrace_append hprefix tailTrace_3751882
  have hstable : (prefixWord ++ tailWord_3751882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751882).length < 2 ^ (prefixWord ++ tailWord_3751882).sum := by decide
  have hdescent : baseEnd_3751882 < baseStart_3751882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751914 : List Nat := [3, 1, 3, 1, 2, 1, 1, 2, 5, 3]
def baseStart_3751914 : Nat := 118140960795 + 3751914 * 2 ^ 59
def prefixEnd_3751914 : Nat := 4983230072969 + 3 ^ 40 * 3751914 * 2
def baseEnd_3751914 : Nat := 1284356837555425901946845

theorem tailTrace_3751914 : CollatzResearch.WordTrace tailWord_3751914 prefixEnd_3751914 1284356837555425901946845 := by
  unfold tailWord_3751914
  simp only [CollatzResearch.WordTrace]
  refine ⟨34210886432365957185383699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91229030486309219161023197 34210886432365957185383699)
  ·
    refine ⟨51316329648548935778075549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34210886432365957185383699 51316329648548935778075549)
    ·
      refine ⟨19243623618205850916778331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51316329648548935778075549 19243623618205850916778331)
      ·
        refine ⟨28865435427308776375167497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19243623618205850916778331 28865435427308776375167497)
        ·
          refine ⟨21649076570481582281375623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28865435427308776375167497 21649076570481582281375623)
          ·
            refine ⟨32473614855722373422063435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21649076570481582281375623 32473614855722373422063435)
            ·
              refine ⟨48710422283583560133095153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32473614855722373422063435 48710422283583560133095153)
              ·
                refine ⟨36532816712687670099821365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48710422283583560133095153 36532816712687670099821365)
                ·
                  refine ⟨3424951566814469071858253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36532816712687670099821365 3424951566814469071858253)
                  ·
                    refine ⟨1284356837555425901946845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3424951566814469071858253 1284356837555425901946845)
                    ·
                      rfl

theorem cell22_3751914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 5, 3].length) (baseStart_3751914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3751914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3751914 prefixEnd_3751914 := by exact prefixLift 3751914
  have htrace : WordTrace (prefixWord ++ tailWord_3751914) baseStart_3751914 baseEnd_3751914 := by
    simpa [prefixWord, tailWord_3751914, baseEnd_3751914] using wordTrace_append hprefix tailTrace_3751914
  have hstable : (prefixWord ++ tailWord_3751914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751914).length < 2 ^ (prefixWord ++ tailWord_3751914).sum := by decide
  have hdescent : baseEnd_3751914 < baseStart_3751914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751931 : List Nat := [1, 1, 1, 1, 1, 3, 6, 4, 1, 3]
def baseStart_3751931 : Nat := 118140960795 + 3751931 * 2 ^ 59
def prefixEnd_3751931 : Nat := 4983230072969 + 3 ^ 40 * 3751931 * 2
def baseEnd_3751931 : Nat := 1284362657002843524271793

theorem tailTrace_3751931 : CollatzResearch.WordTrace tailWord_3751931 prefixEnd_3751931 1284362657002843524271793 := by
  unfold tailWord_3751931
  simp only [CollatzResearch.WordTrace]
  refine ⟨136844165770402240644903647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91229443846934827096602431 136844165770402240644903647)
  ·
    refine ⟨205266248655603360967355471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136844165770402240644903647 205266248655603360967355471)
    ·
      refine ⟨307899372983405041451033207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205266248655603360967355471 307899372983405041451033207)
      ·
        refine ⟨461849059475107562176549811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307899372983405041451033207 461849059475107562176549811)
        ·
          refine ⟨692773589212661343264824717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 461849059475107562176549811 692773589212661343264824717)
          ·
            refine ⟨259790095954748003724309269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 692773589212661343264824717 259790095954748003724309269)
            ·
              refine ⟨12177660747878812674576997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 259790095954748003724309269 12177660747878812674576997)
              ·
                refine ⟨2283311390227277376483187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12177660747878812674576997 2283311390227277376483187)
                ·
                  refine ⟨3424967085340916064724781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2283311390227277376483187 3424967085340916064724781)
                  ·
                    refine ⟨1284362657002843524271793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3424967085340916064724781 1284362657002843524271793)
                    ·
                      rfl

theorem cell22_3751931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 4, 1, 3].length) (baseStart_3751931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3751931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3751931 prefixEnd_3751931 := by exact prefixLift 3751931
  have htrace : WordTrace (prefixWord ++ tailWord_3751931) baseStart_3751931 baseEnd_3751931 := by
    simpa [prefixWord, tailWord_3751931, baseEnd_3751931] using wordTrace_append hprefix tailTrace_3751931
  have hstable : (prefixWord ++ tailWord_3751931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751931).length < 2 ^ (prefixWord ++ tailWord_3751931).sum := by decide
  have hdescent : baseEnd_3751931 < baseStart_3751931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751965 : List Nat := [1, 4, 2, 2, 2, 3, 1, 3, 1, 3]
def baseStart_3751965 : Nat := 118140960795 + 3751965 * 2 ^ 59
def prefixEnd_3751965 : Nat := 4983230072969 + 3 ^ 40 * 3751965 * 2
def baseEnd_3751965 : Nat := 1284374295897678768921689

theorem tailTrace_3751965 : CollatzResearch.WordTrace tailWord_3751965 prefixEnd_3751965 1284374295897678768921689 := by
  unfold tailWord_3751965
  simp only [CollatzResearch.WordTrace]
  refine ⟨136845405852279064451641349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91230270568186042967760899 136845405852279064451641349)
  ·
    refine ⟨25658513597302324584682753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136845405852279064451641349 25658513597302324584682753)
    ·
      refine ⟨19243885197976743438512065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25658513597302324584682753 19243885197976743438512065)
      ·
        refine ⟨14432913898482557578884049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19243885197976743438512065 14432913898482557578884049)
        ·
          refine ⟨10824685423861918184163037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14432913898482557578884049 10824685423861918184163037)
          ·
            refine ⟨4059257033948219319061139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10824685423861918184163037 4059257033948219319061139)
            ·
              refine ⟨6088885550922328978591709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4059257033948219319061139 6088885550922328978591709)
              ·
                refine ⟨2283332081595873366971891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6088885550922328978591709 2283332081595873366971891)
                ·
                  refine ⟨3424998122393810050457837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2283332081595873366971891 3424998122393810050457837)
                  ·
                    refine ⟨1284374295897678768921689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3424998122393810050457837 1284374295897678768921689)
                    ·
                      rfl

theorem cell22_3751965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 3, 1, 3].length) (baseStart_3751965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3751965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3751965 prefixEnd_3751965 := by exact prefixLift 3751965
  have htrace : WordTrace (prefixWord ++ tailWord_3751965) baseStart_3751965 baseEnd_3751965 := by
    simpa [prefixWord, tailWord_3751965, baseEnd_3751965] using wordTrace_append hprefix tailTrace_3751965
  have hstable : (prefixWord ++ tailWord_3751965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751965).length < 2 ^ (prefixWord ++ tailWord_3751965).sum := by decide
  have hdescent : baseEnd_3751965 < baseStart_3751965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751989 : List Nat := [1, 3, 3, 1, 1, 1, 5, 1, 6]
def baseStart_3751989 : Nat := 118140960795 + 3751989 * 2 ^ 59
def prefixEnd_3751989 : Nat := 4983230072969 + 3 ^ 40 * 3751989 * 2
def baseEnd_3751989 : Nat := 428127503862716902107205

theorem tailTrace_3751989 : CollatzResearch.WordTrace tailWord_3751989 prefixEnd_3751989 428127503862716902107205 := by
  unfold tailWord_3751989
  simp only [CollatzResearch.WordTrace]
  refine ⟨136846281204192116550515021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91230854136128077700343347 136846281204192116550515021)
  ·
    refine ⟨51317355451572043706443133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136846281204192116550515021 51317355451572043706443133)
    ·
      refine ⟨19244008294339516389916175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51317355451572043706443133 19244008294339516389916175)
      ·
        refine ⟨28866012441509274584874263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19244008294339516389916175 28866012441509274584874263)
        ·
          refine ⟨43299018662263911877311395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28866012441509274584874263 43299018662263911877311395)
          ·
            refine ⟨64948527993395867815967093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43299018662263911877311395 64948527993395867815967093)
            ·
              refine ⟨6088924499380862607746915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64948527993395867815967093 6088924499380862607746915)
              ·
                refine ⟨9133386749071293911620373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6088924499380862607746915 9133386749071293911620373)
                ·
                  refine ⟨428127503862716902107205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9133386749071293911620373 428127503862716902107205)
                  ·
                    rfl

theorem cell22_3751989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 1, 6].length) (baseStart_3751989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3751989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3751989 prefixEnd_3751989 := by exact prefixLift 3751989
  have htrace : WordTrace (prefixWord ++ tailWord_3751989) baseStart_3751989 baseEnd_3751989 := by
    simpa [prefixWord, tailWord_3751989, baseEnd_3751989] using wordTrace_append hprefix tailTrace_3751989
  have hstable : (prefixWord ++ tailWord_3751989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751989).length < 2 ^ (prefixWord ++ tailWord_3751989).sum := by decide
  have hdescent : baseEnd_3751989 < baseStart_3751989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752006 : List Nat := [6, 1, 1, 1, 1, 1, 2, 1, 8]
def baseStart_3752006 : Nat := 118140960795 + 3752006 * 2 ^ 59
def prefixEnd_3752006 : Nat := 4983230072969 + 3 ^ 40 * 3752006 * 2
def baseEnd_3752006 : Nat := 428129443678522776215521

theorem tailTrace_3752006 : CollatzResearch.WordTrace tailWord_3752006 prefixEnd_3752006 428129443678522776215521 := by
  unfold tailWord_3752006
  simp only [CollatzResearch.WordTrace]
  refine ⟨4276465663910329014183871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 91231267496753685635922581 4276465663910329014183871)
  ·
    refine ⟨6414698495865493521275807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4276465663910329014183871 6414698495865493521275807)
    ·
      refine ⟨9622047743798240281913711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6414698495865493521275807 9622047743798240281913711)
      ·
        refine ⟨14433071615697360422870567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9622047743798240281913711 14433071615697360422870567)
        ·
          refine ⟨21649607423546040634305851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14433071615697360422870567 21649607423546040634305851)
          ·
            refine ⟨32474411135319060951458777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21649607423546040634305851 32474411135319060951458777)
            ·
              refine ⟨24355808351489295713594083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32474411135319060951458777 24355808351489295713594083)
              ·
                refine ⟨36533712527233943570391125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24355808351489295713594083 36533712527233943570391125)
                ·
                  refine ⟨428129443678522776215521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36533712527233943570391125 428129443678522776215521)
                  ·
                    rfl

theorem cell22_3752006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_3752006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3752006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3752006 prefixEnd_3752006 := by exact prefixLift 3752006
  have htrace : WordTrace (prefixWord ++ tailWord_3752006) baseStart_3752006 baseEnd_3752006 := by
    simpa [prefixWord, tailWord_3752006, baseEnd_3752006] using wordTrace_append hprefix tailTrace_3752006
  have hstable : (prefixWord ++ tailWord_3752006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752006).length < 2 ^ (prefixWord ++ tailWord_3752006).sum := by decide
  have hdescent : baseEnd_3752006 < baseStart_3752006 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752034 : List Nat := [3, 3, 2, 2, 12]
def baseStart_3752034 : Nat := 118140960795 + 3752034 * 2 ^ 59
def prefixEnd_3752034 : Nat := 4983230072969 + 3 ^ 40 * 3752034 * 2
def baseEnd_3752034 : Nat := 5285588131719282259039

theorem tailTrace_3752034 : CollatzResearch.WordTrace tailWord_3752034 prefixEnd_3752034 5285588131719282259039 := by
  unfold tailWord_3752034
  simp only [CollatzResearch.WordTrace]
  refine ⟨34211980622257272308975789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91231948326019392823935437 34211980622257272308975789)
  ·
    refine ⟨12829492733346477115865921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34211980622257272308975789 12829492733346477115865921)
    ·
      refine ⟨9622119550009857836899441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12829492733346477115865921 9622119550009857836899441)
      ·
        refine ⟨7216589662507393377674581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9622119550009857836899441 7216589662507393377674581)
        ·
          refine ⟨5285588131719282259039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 7216589662507393377674581 5285588131719282259039)
          ·
            rfl

theorem cell22_3752034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 12].length) (baseStart_3752034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3752034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3752034 prefixEnd_3752034 := by exact prefixLift 3752034
  have htrace : WordTrace (prefixWord ++ tailWord_3752034) baseStart_3752034 baseEnd_3752034 := by
    simpa [prefixWord, tailWord_3752034, baseEnd_3752034] using wordTrace_append hprefix tailTrace_3752034
  have hstable : (prefixWord ++ tailWord_3752034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752034).length < 2 ^ (prefixWord ++ tailWord_3752034).sum := by decide
  have hdescent : baseEnd_3752034 < baseStart_3752034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752096 : List Nat := [2, 1, 1, 4, 2, 2, 3, 2, 5]
def baseStart_3752096 : Nat := 118140960795 + 3752096 * 2 ^ 59
def prefixEnd_3752096 : Nat := 4983230072969 + 3 ^ 40 * 3752096 * 2
def baseEnd_3752096 : Nat := 428139713291612697965429

theorem tailTrace_3752096 : CollatzResearch.WordTrace tailWord_3752096 prefixEnd_3752096 428139713291612697965429 := by
  unfold tailWord_3752096
  simp only [CollatzResearch.WordTrace]
  refine ⟨68425091907402236912330071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91233455876536315883106761 68425091907402236912330071)
  ·
    refine ⟨102637637861103355368495107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68425091907402236912330071 102637637861103355368495107)
    ·
      refine ⟨153956456791655033052742661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102637637861103355368495107 153956456791655033052742661)
      ·
        refine ⟨28866835648435318697389249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153956456791655033052742661 28866835648435318697389249)
        ·
          refine ⟨21650126736326489023041937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28866835648435318697389249 21650126736326489023041937)
          ·
            refine ⟨16237595052244866767281453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21650126736326489023041937 16237595052244866767281453)
            ·
              refine ⟨6089098144591825037730545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16237595052244866767281453 6089098144591825037730545)
              ·
                refine ⟨4566823608443868778297909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6089098144591825037730545 4566823608443868778297909)
                ·
                  refine ⟨428139713291612697965429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4566823608443868778297909 428139713291612697965429)
                  ·
                    rfl

theorem cell22_3752096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 2, 5].length) (baseStart_3752096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3752096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3752096 prefixEnd_3752096 := by exact prefixLift 3752096
  have htrace : WordTrace (prefixWord ++ tailWord_3752096) baseStart_3752096 baseEnd_3752096 := by
    simpa [prefixWord, tailWord_3752096, baseEnd_3752096] using wordTrace_append hprefix tailTrace_3752096
  have hstable : (prefixWord ++ tailWord_3752096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752096).length < 2 ^ (prefixWord ++ tailWord_3752096).sum := by decide
  have hdescent : baseEnd_3752096 < baseStart_3752096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752139 : List Nat := [1, 1, 1, 1, 3, 2, 4, 1, 3, 5]
def baseStart_3752139 : Nat := 118140960795 + 3752139 * 2 ^ 59
def prefixEnd_3752139 : Nat := 4983230072969 + 3 ^ 40 * 3752139 * 2
def baseEnd_3752139 : Nat := 1284433859653600315071155

theorem tailTrace_3752139 : CollatzResearch.WordTrace tailWord_3752139 prefixEnd_3752139 1284433859653600315071155 := by
  unfold tailWord_3752139
  simp only [CollatzResearch.WordTrace]
  refine ⟨136851752153648692168475471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91234501435765794778983647 136851752153648692168475471)
  ·
    refine ⟨205277628230473038252713207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136851752153648692168475471 205277628230473038252713207)
    ·
      refine ⟨307916442345709557379069811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205277628230473038252713207 307916442345709557379069811)
      ·
        refine ⟨461874663518564336068604717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307916442345709557379069811 461874663518564336068604717)
        ·
          refine ⟨173202998819461626025726769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 461874663518564336068604717 173202998819461626025726769)
          ·
            refine ⟨129902249114596219519295077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173202998819461626025726769 129902249114596219519295077)
            ·
              refine ⟨24356671708986791159867827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129902249114596219519295077 24356671708986791159867827)
              ·
                refine ⟨36535007563480186739801741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24356671708986791159867827 36535007563480186739801741)
                ·
                  refine ⟨13700627836305070027425653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36535007563480186739801741 13700627836305070027425653)
                  ·
                    refine ⟨1284433859653600315071155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13700627836305070027425653 1284433859653600315071155)
                    ·
                      rfl

theorem cell22_3752139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 3, 5].length) (baseStart_3752139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3752139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3752139 prefixEnd_3752139 := by exact prefixLift 3752139
  have htrace : WordTrace (prefixWord ++ tailWord_3752139) baseStart_3752139 baseEnd_3752139 := by
    simpa [prefixWord, tailWord_3752139, baseEnd_3752139] using wordTrace_append hprefix tailTrace_3752139
  have hstable : (prefixWord ++ tailWord_3752139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752139).length < 2 ^ (prefixWord ++ tailWord_3752139).sum := by decide
  have hdescent : baseEnd_3752139 < baseStart_3752139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752184 : List Nat := [2, 1, 2, 1, 1, 2, 1, 3, 2, 7]
def baseStart_3752184 : Nat := 118140960795 + 3752184 * 2 ^ 59
def prefixEnd_3752184 : Nat := 4983230072969 + 3 ^ 40 * 3752184 * 2
def baseEnd_3752184 : Nat := 1284449264073235197696017

theorem tailTrace_3752184 : CollatzResearch.WordTrace tailWord_3752184 prefixEnd_3752184 1284449264073235197696017 := by
  unfold tailWord_3752184
  simp only [CollatzResearch.WordTrace]
  refine ⟨68426696719242832426931803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91235595625657109902575737 68426696719242832426931803)
  ·
    refine ⟨102640045078864248640397705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68426696719242832426931803 102640045078864248640397705)
    ·
      refine ⟨76980033809148186480298279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102640045078864248640397705 76980033809148186480298279)
      ·
        refine ⟨115470050713722279720447419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76980033809148186480298279 115470050713722279720447419)
        ·
          refine ⟨173205076070583419580671129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115470050713722279720447419 173205076070583419580671129)
          ·
            refine ⟨129903807052937564685503347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173205076070583419580671129 129903807052937564685503347)
            ·
              refine ⟨194855710579406347028255021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129903807052937564685503347 194855710579406347028255021)
              ·
                refine ⟨73070891467277380135595633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 194855710579406347028255021 73070891467277380135595633)
                ·
                  refine ⟨54803168600458035101696725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73070891467277380135595633 54803168600458035101696725)
                  ·
                    refine ⟨1284449264073235197696017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54803168600458035101696725 1284449264073235197696017)
                    ·
                      rfl

theorem cell22_3752184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 2, 7].length) (baseStart_3752184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3752184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3752184 prefixEnd_3752184 := by exact prefixLift 3752184
  have htrace : WordTrace (prefixWord ++ tailWord_3752184) baseStart_3752184 baseEnd_3752184 := by
    simpa [prefixWord, tailWord_3752184, baseEnd_3752184] using wordTrace_append hprefix tailTrace_3752184
  have hstable : (prefixWord ++ tailWord_3752184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752184).length < 2 ^ (prefixWord ++ tailWord_3752184).sum := by decide
  have hdescent : baseEnd_3752184 < baseStart_3752184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752188 : List Nat := [2, 2, 2, 1, 4, 2, 2, 1, 2, 4]
def baseStart_3752188 : Nat := 118140960795 + 3752188 * 2 ^ 59
def prefixEnd_3752188 : Nat := 4983230072969 + 3 ^ 40 * 3752188 * 2
def baseEnd_3752188 : Nat := 1284450633354980520596005

theorem tailTrace_3752188 : CollatzResearch.WordTrace tailWord_3752188 prefixEnd_3752188 1284450633354980520596005 := by
  unfold tailWord_3752188
  simp only [CollatzResearch.WordTrace]
  refine ⟨68426769665235586768504609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91235692886980782358006145 68426769665235586768504609)
  ·
    refine ⟨51320077248926690076378457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68426769665235586768504609 51320077248926690076378457)
    ·
      refine ⟨38490057936695017557283843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51320077248926690076378457 38490057936695017557283843)
      ·
        refine ⟨57735086905042526335925765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38490057936695017557283843 57735086905042526335925765)
        ·
          refine ⟨10825328794695473687986081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57735086905042526335925765 10825328794695473687986081)
          ·
            refine ⟨8118996596021605265989561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10825328794695473687986081 8118996596021605265989561)
            ·
              refine ⟨6089247447016203949492171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8118996596021605265989561 6089247447016203949492171)
              ·
                refine ⟨9133871170524305924238257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6089247447016203949492171 9133871170524305924238257)
                ·
                  refine ⟨6850403377893229443178693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9133871170524305924238257 6850403377893229443178693)
                  ·
                    refine ⟨1284450633354980520596005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6850403377893229443178693 1284450633354980520596005)
                    ·
                      rfl

theorem cell22_3752188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 1, 2, 4].length) (baseStart_3752188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3752188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3752188 prefixEnd_3752188 := by exact prefixLift 3752188
  have htrace : WordTrace (prefixWord ++ tailWord_3752188) baseStart_3752188 baseEnd_3752188 := by
    simpa [prefixWord, tailWord_3752188, baseEnd_3752188] using wordTrace_append hprefix tailTrace_3752188
  have hstable : (prefixWord ++ tailWord_3752188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752188).length < 2 ^ (prefixWord ++ tailWord_3752188).sum := by decide
  have hdescent : baseEnd_3752188 < baseStart_3752188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752295 : List Nat := [1, 1, 5, 1, 3, 2, 2, 2, 1, 4]
def baseStart_3752295 : Nat := 118140960795 + 3752295 * 2 ^ 59
def prefixEnd_3752295 : Nat := 4983230072969 + 3 ^ 40 * 3752295 * 2
def baseEnd_3752295 : Nat := 1284487261641667908170677

theorem tailTrace_3752295 : CollatzResearch.WordTrace tailWord_3752295 prefixEnd_3752295 1284487261641667908170677 := by
  unfold tailWord_3752295
  simp only [CollatzResearch.WordTrace]
  refine ⟨136857441941083530811154339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91238294627389020540769559 136857441941083530811154339)
  ·
    refine ⟨205286162911625296216731509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136857441941083530811154339 205286162911625296216731509)
    ·
      refine ⟨19245577772964871520318579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 205286162911625296216731509 19245577772964871520318579)
      ·
        refine ⟨28868366659447307280477869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19245577772964871520318579 28868366659447307280477869)
        ·
          refine ⟨10825637497292740230179201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28868366659447307280477869 10825637497292740230179201)
          ·
            refine ⟨8119228122969555172634401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10825637497292740230179201 8119228122969555172634401)
            ·
              refine ⟨6089421092227166379475801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8119228122969555172634401 6089421092227166379475801)
              ·
                refine ⟨4567065819170374784606851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6089421092227166379475801 4567065819170374784606851)
                ·
                  refine ⟨6850598728755562176910277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4567065819170374784606851 6850598728755562176910277)
                  ·
                    refine ⟨1284487261641667908170677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6850598728755562176910277 1284487261641667908170677)
                    ·
                      rfl

theorem cell22_3752295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_3752295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3752295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3752295 prefixEnd_3752295 := by exact prefixLift 3752295
  have htrace : WordTrace (prefixWord ++ tailWord_3752295) baseStart_3752295 baseEnd_3752295 := by
    simpa [prefixWord, tailWord_3752295, baseEnd_3752295] using wordTrace_append hprefix tailTrace_3752295
  have hstable : (prefixWord ++ tailWord_3752295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752295).length < 2 ^ (prefixWord ++ tailWord_3752295).sum := by decide
  have hdescent : baseEnd_3752295 < baseStart_3752295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752372 : List Nat := [2, 5, 2, 2, 2, 9]
def baseStart_3752372 : Nat := 118140960795 + 3752372 * 2 ^ 59
def prefixEnd_3752372 : Nat := 4983230072969 + 3 ^ 40 * 3752372 * 2
def baseEnd_3752372 : Nat := 15858192843398337950561

theorem tailTrace_3752372 : CollatzResearch.WordTrace tailWord_3752372 prefixEnd_3752372 15858192843398337950561 := by
  unfold tailWord_3752372
  simp only [CollatzResearch.WordTrace]
  refine ⟨68430125180902286480853685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91240166907869715307804913 68430125180902286480853685)
  ·
    refine ⟨6415324235709589357580033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68430125180902286480853685 6415324235709589357580033)
    ·
      refine ⟨4811493176782192018185025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6415324235709589357580033 4811493176782192018185025)
      ·
        refine ⟨3608619882586644013638769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4811493176782192018185025 3608619882586644013638769)
        ·
          refine ⟨2706464911939983010229077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3608619882586644013638769 2706464911939983010229077)
          ·
            refine ⟨15858192843398337950561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2706464911939983010229077 15858192843398337950561)
            ·
              rfl

theorem cell22_3752372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 9].length) (baseStart_3752372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3752372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3752372 prefixEnd_3752372 := by exact prefixLift 3752372
  have htrace : WordTrace (prefixWord ++ tailWord_3752372) baseStart_3752372 baseEnd_3752372 := by
    simpa [prefixWord, tailWord_3752372, baseEnd_3752372] using wordTrace_append hprefix tailTrace_3752372
  have hstable : (prefixWord ++ tailWord_3752372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752372).length < 2 ^ (prefixWord ++ tailWord_3752372).sum := by decide
  have hdescent : baseEnd_3752372 < baseStart_3752372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752434 : List Nat := [3, 2, 1, 4, 3, 1, 1, 2, 5]
def baseStart_3752434 : Nat := 118140960795 + 3752434 * 2 ^ 59
def prefixEnd_3752434 : Nat := 4983230072969 + 3 ^ 40 * 3752434 * 2
def baseEnd_3752434 : Nat := 428178281394105959648417

theorem tailTrace_3752434 : CollatzResearch.WordTrace tailWord_3752434 prefixEnd_3752434 428178281394105959648417 := by
  unfold tailWord_3752434
  simp only [CollatzResearch.WordTrace]
  refine ⟨34215627921894989387616089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91241674458386638366976237 34215627921894989387616089)
  ·
    refine ⟨25661720941421242040712067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34215627921894989387616089 25661720941421242040712067)
    ·
      refine ⟨38492581412131863061068101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25661720941421242040712067 38492581412131863061068101)
      ·
        refine ⟨7217359014774724323950269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38492581412131863061068101 7217359014774724323950269)
        ·
          refine ⟨2706509630540521621481351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7217359014774724323950269 2706509630540521621481351)
          ·
            refine ⟨4059764445810782432222027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2706509630540521621481351 4059764445810782432222027)
            ·
              refine ⟨6089646668716173648333041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4059764445810782432222027 6089646668716173648333041)
              ·
                refine ⟨4567235001537130236249781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6089646668716173648333041 4567235001537130236249781)
                ·
                  refine ⟨428178281394105959648417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4567235001537130236249781 428178281394105959648417)
                  ·
                    rfl

theorem cell22_3752434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 2, 5].length) (baseStart_3752434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3752434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3752434 prefixEnd_3752434 := by exact prefixLift 3752434
  have htrace : WordTrace (prefixWord ++ tailWord_3752434) baseStart_3752434 baseEnd_3752434 := by
    simpa [prefixWord, tailWord_3752434, baseEnd_3752434] using wordTrace_append hprefix tailTrace_3752434
  have hstable : (prefixWord ++ tailWord_3752434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752434).length < 2 ^ (prefixWord ++ tailWord_3752434).sum := by decide
  have hdescent : baseEnd_3752434 < baseStart_3752434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752445 : List Nat := [1, 4, 1, 1, 1, 3, 1, 6, 4]
def baseStart_3752445 : Nat := 118140960795 + 3752445 * 2 ^ 59
def prefixEnd_3752445 : Nat := 4983230072969 + 3 ^ 40 * 3752445 * 2
def baseEnd_3752445 : Nat := 428179536569039172306739

theorem tailTrace_3752445 : CollatzResearch.WordTrace tailWord_3752445 prefixEnd_3752445 428179536569039172306739 := by
  unfold tailWord_3752445
  simp only [CollatzResearch.WordTrace]
  refine ⟨136862912890540106429114789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91241941927026737619409859 136862912890540106429114789)
  ·
    refine ⟨25661796166976269955459023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136862912890540106429114789 25661796166976269955459023)
    ·
      refine ⟨38492694250464404933188535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25661796166976269955459023 38492694250464404933188535)
      ·
        refine ⟨57739041375696607399782803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38492694250464404933188535 57739041375696607399782803)
        ·
          refine ⟨86608562063544911099674205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57739041375696607399782803 86608562063544911099674205)
          ·
            refine ⟨32478210773829341662377827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86608562063544911099674205 32478210773829341662377827)
            ·
              refine ⟨48717316160744012493566741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32478210773829341662377827 48717316160744012493566741)
              ·
                refine ⟨2283624195034875585635941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 48717316160744012493566741 2283624195034875585635941)
                ·
                  refine ⟨428179536569039172306739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2283624195034875585635941 428179536569039172306739)
                  ·
                    rfl

theorem cell22_3752445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 6, 4].length) (baseStart_3752445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3752445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3752445 prefixEnd_3752445 := by exact prefixLift 3752445
  have htrace : WordTrace (prefixWord ++ tailWord_3752445) baseStart_3752445 baseEnd_3752445 := by
    simpa [prefixWord, tailWord_3752445, baseEnd_3752445] using wordTrace_append hprefix tailTrace_3752445
  have hstable : (prefixWord ++ tailWord_3752445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752445).length < 2 ^ (prefixWord ++ tailWord_3752445).sum := by decide
  have hdescent : baseEnd_3752445 < baseStart_3752445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752458 : List Nat := [3, 1, 2, 2, 2, 1, 1, 1, 3, 6]
def baseStart_3752458 : Nat := 118140960795 + 3752458 * 2 ^ 59
def prefixEnd_3752458 : Nat := 4983230072969 + 3 ^ 40 * 3752458 * 2
def baseEnd_3752458 : Nat := 1284543059872789816345177

theorem tailTrace_3752458 : CollatzResearch.WordTrace tailWord_3752458 prefixEnd_3752458 1284543059872789816345177 := by
  unfold tailWord_3752458
  simp only [CollatzResearch.WordTrace]
  refine ⟨34215846759873252412334507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91242258026328673099558685 34215846759873252412334507)
  ·
    refine ⟨51323770139809878618501761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34215846759873252412334507 51323770139809878618501761)
    ·
      refine ⟨38492827604857408963876321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51323770139809878618501761 38492827604857408963876321)
      ·
        refine ⟨28869620703643056722907241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38492827604857408963876321 28869620703643056722907241)
        ·
          refine ⟨21652215527732292542180431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28869620703643056722907241 21652215527732292542180431)
          ·
            refine ⟨32478323291598438813270647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21652215527732292542180431 32478323291598438813270647)
            ·
              refine ⟨48717484937397658219905971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32478323291598438813270647 48717484937397658219905971)
              ·
                refine ⟨73076227406096487329858957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48717484937397658219905971 73076227406096487329858957)
                ·
                  refine ⟨27403585277286182748697109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73076227406096487329858957 27403585277286182748697109)
                  ·
                    refine ⟨1284543059872789816345177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27403585277286182748697109 1284543059872789816345177)
                    ·
                      rfl

theorem cell22_3752458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_3752458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3752458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3752458 prefixEnd_3752458 := by exact prefixLift 3752458
  have htrace : WordTrace (prefixWord ++ tailWord_3752458) baseStart_3752458 baseEnd_3752458 := by
    simpa [prefixWord, tailWord_3752458, baseEnd_3752458] using wordTrace_append hprefix tailTrace_3752458
  have hstable : (prefixWord ++ tailWord_3752458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752458).length < 2 ^ (prefixWord ++ tailWord_3752458).sum := by decide
  have hdescent : baseEnd_3752458 < baseStart_3752458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752460 : List Nat := [2, 2, 1, 2, 4, 1, 3, 1, 1, 5]
def baseStart_3752460 : Nat := 118140960795 + 3752460 * 2 ^ 59
def prefixEnd_3752460 : Nat := 4983230072969 + 3 ^ 40 * 3752460 * 2
def baseEnd_3752460 : Nat := 1284543744513662477795171

theorem tailTrace_3752460 : CollatzResearch.WordTrace tailWord_3752460 prefixEnd_3752460 1284543744513662477795171 := by
  unfold tailWord_3752460
  simp only [CollatzResearch.WordTrace]
  refine ⟨68431729992742881995455417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91242306656990509327273889 68431729992742881995455417)
  ·
    refine ⟨51323797494557161496591563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68431729992742881995455417 51323797494557161496591563)
    ·
      refine ⟨76985696241835742244887345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51323797494557161496591563 76985696241835742244887345)
      ·
        refine ⟨57739272181376806683665509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76985696241835742244887345 57739272181376806683665509)
        ·
          refine ⟨10826113534008151253187283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57739272181376806683665509 10826113534008151253187283)
          ·
            refine ⟨16239170301012226879780925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10826113534008151253187283 16239170301012226879780925)
            ·
              refine ⟨6089688862879585079917847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16239170301012226879780925 6089688862879585079917847)
              ·
                refine ⟨9134533294319377619876771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6089688862879585079917847 9134533294319377619876771)
                ·
                  refine ⟨13701799941479066429815157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9134533294319377619876771 13701799941479066429815157)
                  ·
                    refine ⟨1284543744513662477795171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13701799941479066429815157 1284543744513662477795171)
                    ·
                      rfl

theorem cell22_3752460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 1, 1, 5].length) (baseStart_3752460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3752460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3752460 prefixEnd_3752460 := by exact prefixLift 3752460
  have htrace : WordTrace (prefixWord ++ tailWord_3752460) baseStart_3752460 baseEnd_3752460 := by
    simpa [prefixWord, tailWord_3752460, baseEnd_3752460] using wordTrace_append hprefix tailTrace_3752460
  have hstable : (prefixWord ++ tailWord_3752460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752460).length < 2 ^ (prefixWord ++ tailWord_3752460).sum := by decide
  have hdescent : baseEnd_3752460 < baseStart_3752460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752490 : List Nat := [3, 1, 4, 1, 1, 4, 8]
def baseStart_3752490 : Nat := 118140960795 + 3752490 * 2 ^ 59
def prefixEnd_3752490 : Nat := 4983230072969 + 3 ^ 40 * 3752490 * 2
def baseEnd_3752490 : Nat := 47576074597287125909077

theorem tailTrace_3752490 : CollatzResearch.WordTrace tailWord_3752490 prefixEnd_3752490 47576074597287125909077 := by
  unfold tailWord_3752490
  simp only [CollatzResearch.WordTrace]
  refine ⟨34216138543844269778625731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91243036116918052743001949 34216138543844269778625731)
  ·
    refine ⟨51324207815766404667938597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34216138543844269778625731 51324207815766404667938597)
    ·
      refine ⟨9623288965456200875238487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51324207815766404667938597 9623288965456200875238487)
      ·
        refine ⟨14434933448184301312857731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9623288965456200875238487 14434933448184301312857731)
        ·
          refine ⟨21652400172276451969286597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14434933448184301312857731 21652400172276451969286597)
          ·
            refine ⟨4059825032301834744241237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21652400172276451969286597 4059825032301834744241237)
            ·
              refine ⟨47576074597287125909077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4059825032301834744241237 47576074597287125909077)
              ·
                rfl

theorem cell22_3752490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 8].length) (baseStart_3752490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3752490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3752490 prefixEnd_3752490 := by exact prefixLift 3752490
  have htrace : WordTrace (prefixWord ++ tailWord_3752490) baseStart_3752490 baseEnd_3752490 := by
    simpa [prefixWord, tailWord_3752490, baseEnd_3752490] using wordTrace_append hprefix tailTrace_3752490
  have hstable : (prefixWord ++ tailWord_3752490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752490).length < 2 ^ (prefixWord ++ tailWord_3752490).sum := by decide
  have hdescent : baseEnd_3752490 < baseStart_3752490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752503 : List Nat := [1, 1, 3, 1, 2, 3, 2, 1, 2, 6]
def baseStart_3752503 : Nat := 118140960795 + 3752503 * 2 ^ 59
def prefixEnd_3752503 : Nat := 4983230072969 + 3 ^ 40 * 3752503 * 2
def baseEnd_3752503 : Nat := 1284558464292424698970039

theorem tailTrace_3752503 : CollatzResearch.WordTrace tailWord_3752503 prefixEnd_3752503 1284558464292424698970039 := by
  unfold tailWord_3752503
  simp only [CollatzResearch.WordTrace]
  refine ⟨136865028324329982334726163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91243352216219988223150775 136865028324329982334726163)
  ·
    refine ⟨205297542486494973502089245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136865028324329982334726163 205297542486494973502089245)
    ·
      refine ⟨76986578432435615063283467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205297542486494973502089245 76986578432435615063283467)
      ·
        refine ⟨115479867648653422594925201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76986578432435615063283467 115479867648653422594925201)
        ·
          refine ⟨86609900736490066946193901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115479867648653422594925201 86609900736490066946193901)
          ·
            refine ⟨32478712776183775104822713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86609900736490066946193901 32478712776183775104822713)
            ·
              refine ⟨24359034582137831328617035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32478712776183775104822713 24359034582137831328617035)
              ·
                refine ⟨36538551873206746992925553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24359034582137831328617035 36538551873206746992925553)
                ·
                  refine ⟨27403913904905060244694165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36538551873206746992925553 27403913904905060244694165)
                  ·
                    refine ⟨1284558464292424698970039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27403913904905060244694165 1284558464292424698970039)
                    ·
                      rfl

theorem cell22_3752503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 6].length) (baseStart_3752503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3752503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3752503 prefixEnd_3752503 := by exact prefixLift 3752503
  have htrace : WordTrace (prefixWord ++ tailWord_3752503) baseStart_3752503 baseEnd_3752503 := by
    simpa [prefixWord, tailWord_3752503, baseEnd_3752503] using wordTrace_append hprefix tailTrace_3752503
  have hstable : (prefixWord ++ tailWord_3752503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752503).length < 2 ^ (prefixWord ++ tailWord_3752503).sum := by decide
  have hdescent : baseEnd_3752503 < baseStart_3752503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752580 : List Nat := [2, 3, 2, 1, 3, 1, 1, 1, 8]
def baseStart_3752580 : Nat := 118140960795 + 3752580 * 2 ^ 59
def prefixEnd_3752580 : Nat := 4983230072969 + 3 ^ 40 * 3752580 * 2
def baseEnd_3752580 : Nat := 428194940988674054931601

theorem tailTrace_3752580 : CollatzResearch.WordTrace tailWord_3752580 prefixEnd_3752580 428194940988674054931601 := by
  unfold tailWord_3752580
  simp only [CollatzResearch.WordTrace]
  refine ⟨68433918372525512242639597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91245224496700682990186129 68433918372525512242639597)
  ·
    refine ⟨25662719389697067090989849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68433918372525512242639597 25662719389697067090989849)
    ·
      refine ⟨19247039542272800318242387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25662719389697067090989849 19247039542272800318242387)
      ·
        refine ⟨28870559313409200477363581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19247039542272800318242387 28870559313409200477363581)
        ·
          refine ⟨10826459742528450179011343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28870559313409200477363581 10826459742528450179011343)
          ·
            refine ⟨16239689613792675268517015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10826459742528450179011343 16239689613792675268517015)
            ·
              refine ⟨24359534420689012902775523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16239689613792675268517015 24359534420689012902775523)
              ·
                refine ⟨36539301631033519354163285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24359534420689012902775523 36539301631033519354163285)
                ·
                  refine ⟨428194940988674054931601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36539301631033519354163285 428194940988674054931601)
                  ·
                    rfl

theorem cell22_3752580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 8].length) (baseStart_3752580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3752580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3752580 prefixEnd_3752580 := by exact prefixLift 3752580
  have htrace : WordTrace (prefixWord ++ tailWord_3752580) baseStart_3752580 baseEnd_3752580 := by
    simpa [prefixWord, tailWord_3752580, baseEnd_3752580] using wordTrace_append hprefix tailTrace_3752580
  have hstable : (prefixWord ++ tailWord_3752580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752580).length < 2 ^ (prefixWord ++ tailWord_3752580).sum := by decide
  have hdescent : baseEnd_3752580 < baseStart_3752580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752595 : List Nat := [1, 1, 1, 2, 1, 2, 2, 3, 6, 3]
def baseStart_3752595 : Nat := 118140960795 + 3752595 * 2 ^ 59
def prefixEnd_3752595 : Nat := 4983230072969 + 3 ^ 40 * 3752595 * 2
def baseEnd_3752595 : Nat := 1284589957772567125669757

theorem tailTrace_3752595 : CollatzResearch.WordTrace tailWord_3752595 prefixEnd_3752595 1284589957772567125669757 := by
  unfold tailWord_3752595
  simp only [CollatzResearch.WordTrace]
  refine ⟨136868383839996682047075239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91245589226664454698050159 136868383839996682047075239)
  ·
    refine ⟨205302575759995023070612859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136868383839996682047075239 205302575759995023070612859)
    ·
      refine ⟨307953863639992534605919289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205302575759995023070612859 307953863639992534605919289)
      ·
        refine ⟨230965397729994400954439467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307953863639992534605919289 230965397729994400954439467)
        ·
          refine ⟨346448096594991601431659201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230965397729994400954439467 346448096594991601431659201)
          ·
            refine ⟨259836072446243701073744401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 346448096594991601431659201 259836072446243701073744401)
            ·
              refine ⟨194877054334682775805308301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 259836072446243701073744401 194877054334682775805308301)
              ·
                refine ⟨73078895375506040926990613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 194877054334682775805308301 73078895375506040926990613)
                ·
                  refine ⟨3425573220726845668452685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 73078895375506040926990613 3425573220726845668452685)
                  ·
                    refine ⟨1284589957772567125669757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3425573220726845668452685 1284589957772567125669757)
                    ·
                      rfl

theorem cell22_3752595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 6, 3].length) (baseStart_3752595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3752595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3752595 prefixEnd_3752595 := by exact prefixLift 3752595
  have htrace : WordTrace (prefixWord ++ tailWord_3752595) baseStart_3752595 baseEnd_3752595 := by
    simpa [prefixWord, tailWord_3752595, baseEnd_3752595] using wordTrace_append hprefix tailTrace_3752595
  have hstable : (prefixWord ++ tailWord_3752595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752595).length < 2 ^ (prefixWord ++ tailWord_3752595).sum := by decide
  have hdescent : baseEnd_3752595 < baseStart_3752595 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752612 : List Nat := [2, 3, 1, 2, 2, 1, 3, 1, 4, 3]
def baseStart_3752612 : Nat := 118140960795 + 3752612 * 2 ^ 59
def prefixEnd_3752612 : Nat := 4983230072969 + 3 ^ 40 * 3752612 * 2
def baseEnd_3752612 : Nat := 1284595777219984747994705

theorem tailTrace_3752612 : CollatzResearch.WordTrace tailWord_3752612 prefixEnd_3752612 1284595777219984747994705 := by
  unfold tailWord_3752612
  simp only [CollatzResearch.WordTrace]
  refine ⟨68434501940467546975222045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91246002587290062633629393 68434501940467546975222045)
  ·
    refine ⟨25662938227675330115708267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68434501940467546975222045 25662938227675330115708267)
    ·
      refine ⟨38494407341512995173562401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25662938227675330115708267 38494407341512995173562401)
      ·
        refine ⟨28870805506134746380171801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38494407341512995173562401 28870805506134746380171801)
        ·
          refine ⟨21653104129601059785128851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28870805506134746380171801 21653104129601059785128851)
          ·
            refine ⟨32479656194401589677693277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21653104129601059785128851 32479656194401589677693277)
            ·
              refine ⟨12179871072900596129134979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32479656194401589677693277 12179871072900596129134979)
              ·
                refine ⟨18269806609350894193702469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12179871072900596129134979 18269806609350894193702469)
                ·
                  refine ⟨3425588739253292661319213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18269806609350894193702469 3425588739253292661319213)
                  ·
                    refine ⟨1284595777219984747994705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3425588739253292661319213 1284595777219984747994705)
                    ·
                      rfl

theorem cell22_3752612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 4, 3].length) (baseStart_3752612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3752612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3752612 prefixEnd_3752612 := by exact prefixLift 3752612
  have htrace : WordTrace (prefixWord ++ tailWord_3752612) baseStart_3752612 baseEnd_3752612 := by
    simpa [prefixWord, tailWord_3752612, baseEnd_3752612] using wordTrace_append hprefix tailTrace_3752612
  have hstable : (prefixWord ++ tailWord_3752612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752612).length < 2 ^ (prefixWord ++ tailWord_3752612).sum := by decide
  have hdescent : baseEnd_3752612 < baseStart_3752612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752629 : List Nat := [1, 3, 3, 3, 1, 3, 1, 1, 1, 5]
def baseStart_3752629 : Nat := 118140960795 + 3752629 * 2 ^ 59
def prefixEnd_3752629 : Nat := 4983230072969 + 3 ^ 40 * 3752629 * 2
def baseEnd_3752629 : Nat := 1284601596667402370319653

theorem tailTrace_3752629 : CollatzResearch.WordTrace tailWord_3752629 prefixEnd_3752629 1284601596667402370319653 := by
  unfold tailWord_3752629
  simp only [CollatzResearch.WordTrace]
  refine ⟨136869623921873505853812941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91246415947915670569208627 136869623921873505853812941)
  ·
    refine ⟨51326108970702564695179853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136869623921873505853812941 51326108970702564695179853)
    ·
      refine ⟨19247290864013461760692445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51326108970702564695179853 19247290864013461760692445)
      ·
        refine ⟨7217734074005048160259667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19247290864013461760692445 7217734074005048160259667)
        ·
          refine ⟨10826601111007572240389501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7217734074005048160259667 10826601111007572240389501)
          ·
            refine ⟨4059975416627839590146063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10826601111007572240389501 4059975416627839590146063)
            ·
              refine ⟨6089963124941759385219095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4059975416627839590146063 6089963124941759385219095)
              ·
                refine ⟨9134944687412639077828643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6089963124941759385219095 9134944687412639077828643)
                ·
                  refine ⟨13702417031118958616742965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9134944687412639077828643 13702417031118958616742965)
                  ·
                    refine ⟨1284601596667402370319653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13702417031118958616742965 1284601596667402370319653)
                    ·
                      rfl

theorem cell22_3752629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 1, 1, 5].length) (baseStart_3752629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3752629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3752629 prefixEnd_3752629 := by exact prefixLift 3752629
  have htrace : WordTrace (prefixWord ++ tailWord_3752629) baseStart_3752629 baseEnd_3752629 := by
    simpa [prefixWord, tailWord_3752629, baseEnd_3752629] using wordTrace_append hprefix tailTrace_3752629
  have hstable : (prefixWord ++ tailWord_3752629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752629).length < 2 ^ (prefixWord ++ tailWord_3752629).sum := by decide
  have hdescent : baseEnd_3752629 < baseStart_3752629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752687 : List Nat := [1, 1, 2, 1, 5, 3, 1, 3, 5]
def baseStart_3752687 : Nat := 118140960795 + 3752687 * 2 ^ 59
def prefixEnd_3752687 : Nat := 4983230072969 + 3 ^ 40 * 3752687 * 2
def baseEnd_3752687 : Nat := 428207150417569850789825

theorem tailTrace_3752687 : CollatzResearch.WordTrace tailWord_3752687 prefixEnd_3752687 428207150417569850789825 := by
  unfold tailWord_3752687
  simp only [CollatzResearch.WordTrace]
  refine ⟨136871739355663381759424315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91247826237108921172949543 136871739355663381759424315)
  ·
    refine ⟨205307609033495072639136473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136871739355663381759424315 205307609033495072639136473)
    ·
      refine ⟨153980706775121304479352355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205307609033495072639136473 153980706775121304479352355)
      ·
        refine ⟨230971060162681956719028533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153980706775121304479352355 230971060162681956719028533)
        ·
          refine ⟨21653536890251433442408925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 230971060162681956719028533 21653536890251433442408925)
          ·
            refine ⟨8120076333844287540903347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21653536890251433442408925 8120076333844287540903347)
            ·
              refine ⟨12180114500766431311355021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8120076333844287540903347 12180114500766431311355021)
              ·
                refine ⟨4567542937787411741758133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12180114500766431311355021 4567542937787411741758133)
                ·
                  refine ⟨428207150417569850789825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4567542937787411741758133 428207150417569850789825)
                  ·
                    rfl

theorem cell22_3752687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 3, 5].length) (baseStart_3752687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3752687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3752687 prefixEnd_3752687 := by exact prefixLift 3752687
  have htrace : WordTrace (prefixWord ++ tailWord_3752687) baseStart_3752687 baseEnd_3752687 := by
    simpa [prefixWord, tailWord_3752687, baseEnd_3752687] using wordTrace_append hprefix tailTrace_3752687
  have hstable : (prefixWord ++ tailWord_3752687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752687).length < 2 ^ (prefixWord ++ tailWord_3752687).sum := by decide
  have hdescent : baseEnd_3752687 < baseStart_3752687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752745 : List Nat := [1, 2, 1, 1, 1, 1, 1, 5, 3, 6]
def baseStart_3752745 : Nat := 118140960795 + 3752745 * 2 ^ 59
def prefixEnd_3752745 : Nat := 4983230072969 + 3 ^ 40 * 3752745 * 2
def baseEnd_3752745 : Nat := 1284641305838016734419297

theorem tailTrace_3752745 : CollatzResearch.WordTrace tailWord_3752745 prefixEnd_3752745 1284641305838016734419297 := by
  unfold tailWord_3752745
  simp only [CollatzResearch.WordTrace]
  refine ⟨136873854789453257665035689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91249236526302171776690459 136873854789453257665035689)
  ·
    refine ⟨102655391092089943248776767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136873854789453257665035689 102655391092089943248776767)
    ·
      refine ⟨153983086638134914873165151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102655391092089943248776767 153983086638134914873165151)
      ·
        refine ⟨230974629957202372309747727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153983086638134914873165151 230974629957202372309747727)
        ·
          refine ⟨346461944935803558464621591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230974629957202372309747727 346461944935803558464621591)
          ·
            refine ⟨519692917403705337696932387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346461944935803558464621591 519692917403705337696932387)
            ·
              refine ⟨779539376105558006545398581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 519692917403705337696932387 779539376105558006545398581)
              ·
                refine ⟨73081816509896063113631117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 779539376105558006545398581 73081816509896063113631117)
                ·
                  refine ⟨27405681191211023667611669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73081816509896063113631117 27405681191211023667611669)
                  ·
                    refine ⟨1284641305838016734419297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27405681191211023667611669 1284641305838016734419297)
                    ·
                      rfl

theorem cell22_3752745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 6].length) (baseStart_3752745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3752745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3752745 prefixEnd_3752745 := by exact prefixLift 3752745
  have htrace : WordTrace (prefixWord ++ tailWord_3752745) baseStart_3752745 baseEnd_3752745 := by
    simpa [prefixWord, tailWord_3752745, baseEnd_3752745] using wordTrace_append hprefix tailTrace_3752745
  have hstable : (prefixWord ++ tailWord_3752745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752745).length < 2 ^ (prefixWord ++ tailWord_3752745).sum := by decide
  have hdescent : baseEnd_3752745 < baseStart_3752745 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752867 : List Nat := [1, 1, 1, 4, 1, 2, 2, 4, 6]
def baseStart_3752867 : Nat := 118140960795 + 3752867 * 2 ^ 59
def prefixEnd_3752867 : Nat := 4983230072969 + 3 ^ 40 * 3752867 * 2
def baseEnd_3752867 : Nat := 428227689643749694289641

theorem tailTrace_3752867 : CollatzResearch.WordTrace tailWord_3752867 prefixEnd_3752867 428227689643749694289641 := by
  unfold tailWord_3752867
  simp only [CollatzResearch.WordTrace]
  refine ⟨136878304495011272500976855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91252202996674181667317903 136878304495011272500976855)
  ·
    refine ⟨205317456742516908751465283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136878304495011272500976855 205317456742516908751465283)
    ·
      refine ⟨307976185113775363127197925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205317456742516908751465283 307976185113775363127197925)
      ·
        refine ⟨57745534708832880586349611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 307976185113775363127197925 57745534708832880586349611)
        ·
          refine ⟨86618302063249320879524417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57745534708832880586349611 86618302063249320879524417)
          ·
            refine ⟨64963726547436990659643313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86618302063249320879524417 64963726547436990659643313)
            ·
              refine ⟨48722794910577742994732485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64963726547436990659643313 48722794910577742994732485)
              ·
                refine ⟨9135524045733326811512341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48722794910577742994732485 9135524045733326811512341)
                ·
                  refine ⟨428227689643749694289641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9135524045733326811512341 428227689643749694289641)
                  ·
                    rfl

theorem cell22_3752867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 4, 6].length) (baseStart_3752867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3752867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3752867 prefixEnd_3752867 := by exact prefixLift 3752867
  have htrace : WordTrace (prefixWord ++ tailWord_3752867) baseStart_3752867 baseEnd_3752867 := by
    simpa [prefixWord, tailWord_3752867, baseEnd_3752867] using wordTrace_append hprefix tailTrace_3752867
  have hstable : (prefixWord ++ tailWord_3752867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752867).length < 2 ^ (prefixWord ++ tailWord_3752867).sum := by decide
  have hdescent : baseEnd_3752867 < baseStart_3752867 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752916 : List Nat := [2, 4, 1, 2, 1, 3, 2, 1, 1, 5]
def baseStart_3752916 : Nat := 118140960795 + 3752916 * 2 ^ 59
def prefixEnd_3752916 : Nat := 4983230072969 + 3 ^ 40 * 3752916 * 2
def baseEnd_3752916 : Nat := 1284699842632629288393773

theorem tailTrace_3752916 : CollatzResearch.WordTrace tailWord_3752916 prefixEnd_3752916 1284699842632629288393773 := by
  unfold tailWord_3752916
  simp only [CollatzResearch.WordTrace]
  refine ⟨68440045835916876934755301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91253394447889169246340401 68440045835916876934755301)
  ·
    refine ⟨12832508594234414425266619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68440045835916876934755301 12832508594234414425266619)
    ·
      refine ⟨19248762891351621637899929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12832508594234414425266619 19248762891351621637899929)
      ·
        refine ⟨14436572168513716228424947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19248762891351621637899929 14436572168513716228424947)
        ·
          refine ⟨21654858252770574342637421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14436572168513716228424947 21654858252770574342637421)
          ·
            refine ⟨8120571844788965378489033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21654858252770574342637421 8120571844788965378489033)
            ·
              refine ⟨6090428883591724033866775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8120571844788965378489033 6090428883591724033866775)
              ·
                refine ⟨9135643325387586050800163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6090428883591724033866775 9135643325387586050800163)
                ·
                  refine ⟨13703464988081379076200245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9135643325387586050800163 13703464988081379076200245)
                  ·
                    refine ⟨1284699842632629288393773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13703464988081379076200245 1284699842632629288393773)
                    ·
                      rfl

theorem cell22_3752916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_3752916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3752916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3752916 prefixEnd_3752916 := by exact prefixLift 3752916
  have htrace : WordTrace (prefixWord ++ tailWord_3752916) baseStart_3752916 baseEnd_3752916 := by
    simpa [prefixWord, tailWord_3752916, baseEnd_3752916] using wordTrace_append hprefix tailTrace_3752916
  have hstable : (prefixWord ++ tailWord_3752916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752916).length < 2 ^ (prefixWord ++ tailWord_3752916).sum := by decide
  have hdescent : baseEnd_3752916 < baseStart_3752916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752944 : List Nat := [2, 1, 1, 1, 3, 2, 1, 1, 7, 3]
def baseStart_3752944 : Nat := 118140960795 + 3752944 * 2 ^ 59
def prefixEnd_3752944 : Nat := 4983230072969 + 3 ^ 40 * 3752944 * 2
def baseEnd_3752944 : Nat := 1284709427604846548693687

theorem tailTrace_3752944 : CollatzResearch.WordTrace tailWord_3752944 prefixEnd_3752944 1284709427604846548693687 := by
  unfold tailWord_3752944
  simp only [CollatzResearch.WordTrace]
  refine ⟨68440556457866157325764943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91254075277154876434353257 68440556457866157325764943)
  ·
    refine ⟨102660834686799235988647415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68440556457866157325764943 102660834686799235988647415)
    ·
      refine ⟨153991252030198853982971123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102660834686799235988647415 153991252030198853982971123)
      ·
        refine ⟨230986878045298280974456685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153991252030198853982971123 230986878045298280974456685)
        ·
          refine ⟨86620079266986855365421257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 230986878045298280974456685 86620079266986855365421257)
          ·
            refine ⟨64965059450240141524065943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86620079266986855365421257 64965059450240141524065943)
            ·
              refine ⟨97447589175360212286098915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64965059450240141524065943 97447589175360212286098915)
              ·
                refine ⟨146171383763040318429148373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97447589175360212286098915 146171383763040318429148373)
                ·
                  refine ⟨3425891806946257463183165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 146171383763040318429148373 3425891806946257463183165)
                  ·
                    refine ⟨1284709427604846548693687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3425891806946257463183165 1284709427604846548693687)
                    ·
                      rfl

theorem cell22_3752944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 7, 3].length) (baseStart_3752944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3752944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3752944 prefixEnd_3752944 := by exact prefixLift 3752944
  have htrace : WordTrace (prefixWord ++ tailWord_3752944) baseStart_3752944 baseEnd_3752944 := by
    simpa [prefixWord, tailWord_3752944, baseEnd_3752944] using wordTrace_append hprefix tailTrace_3752944
  have hstable : (prefixWord ++ tailWord_3752944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752944).length < 2 ^ (prefixWord ++ tailWord_3752944).sum := by decide
  have hdescent : baseEnd_3752944 < baseStart_3752944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752946 : List Nat := [3, 2, 1, 5, 1, 1, 9]
def baseStart_3752946 : Nat := 118140960795 + 3752946 * 2 ^ 59
def prefixEnd_3752946 : Nat := 4983230072969 + 3 ^ 40 * 3752946 * 2
def baseEnd_3752946 : Nat := 47581856009100711486803

theorem tailTrace_3752946 : CollatzResearch.WordTrace tailWord_3752946 prefixEnd_3752946 47581856009100711486803 := by
  unfold tailWord_3752946
  simp only [CollatzResearch.WordTrace]
  refine ⟨34220296465431267248275673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91254123907816712662068461 34220296465431267248275673)
  ·
    refine ⟨25665222349073450436206755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34220296465431267248275673 25665222349073450436206755)
    ·
      refine ⟨38497833523610175654310133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25665222349073450436206755 38497833523610175654310133)
      ·
        refine ⟨3609171892838453967591575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38497833523610175654310133 3609171892838453967591575)
        ·
          refine ⟨5413757839257680951387363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3609171892838453967591575 5413757839257680951387363)
          ·
            refine ⟨8120636758886521427081045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5413757839257680951387363 8120636758886521427081045)
            ·
              refine ⟨47581856009100711486803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8120636758886521427081045 47581856009100711486803)
              ·
                rfl

theorem cell22_3752946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 9].length) (baseStart_3752946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3752946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3752946 prefixEnd_3752946 := by exact prefixLift 3752946
  have htrace : WordTrace (prefixWord ++ tailWord_3752946) baseStart_3752946 baseEnd_3752946 := by
    simpa [prefixWord, tailWord_3752946, baseEnd_3752946] using wordTrace_append hprefix tailTrace_3752946
  have hstable : (prefixWord ++ tailWord_3752946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752946).length < 2 ^ (prefixWord ++ tailWord_3752946).sum := by decide
  have hdescent : baseEnd_3752946 < baseStart_3752946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752950 : List Nat := [5, 1, 1, 1, 3, 3, 1, 2, 2, 3]
def baseStart_3752950 : Nat := 118140960795 + 3752950 * 2 ^ 59
def prefixEnd_3752950 : Nat := 4983230072969 + 3 ^ 40 * 3752950 * 2
def baseEnd_3752950 : Nat := 1284711481527464533043669

theorem tailTrace_3752950 : CollatzResearch.WordTrace tailWord_3752950 prefixEnd_3752950 1284711481527464533043669 := by
  unfold tailWord_3752950
  simp only [CollatzResearch.WordTrace]
  refine ⟨8555083234606911104765519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91254221169140385117498869 8555083234606911104765519)
  ·
    refine ⟨12832624851910366657148279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8555083234606911104765519 12832624851910366657148279)
    ·
      refine ⟨19248937277865549985722419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12832624851910366657148279 19248937277865549985722419)
      ·
        refine ⟨28873405916798324978583629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19248937277865549985722419 28873405916798324978583629)
        ·
          refine ⟨10827527218799371866968861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28873405916798324978583629 10827527218799371866968861)
          ·
            refine ⟨4060322707049764450113323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10827527218799371866968861 4060322707049764450113323)
            ·
              refine ⟨6090484060574646675169985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4060322707049764450113323 6090484060574646675169985)
              ·
                refine ⟨4567863045430985006377489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6090484060574646675169985 4567863045430985006377489)
                ·
                  refine ⟨3425897284073238754783117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4567863045430985006377489 3425897284073238754783117)
                  ·
                    refine ⟨1284711481527464533043669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3425897284073238754783117 1284711481527464533043669)
                    ·
                      rfl

theorem cell22_3752950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 2, 2, 3].length) (baseStart_3752950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3752950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3752950 prefixEnd_3752950 := by exact prefixLift 3752950
  have htrace : WordTrace (prefixWord ++ tailWord_3752950) baseStart_3752950 baseEnd_3752950 := by
    simpa [prefixWord, tailWord_3752950, baseEnd_3752950] using wordTrace_append hprefix tailTrace_3752950
  have hstable : (prefixWord ++ tailWord_3752950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752950).length < 2 ^ (prefixWord ++ tailWord_3752950).sum := by decide
  have hdescent : baseEnd_3752950 < baseStart_3752950 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752961 : List Nat := [1, 2, 4, 1, 2, 2, 1, 3, 3, 3]
def baseStart_3752961 : Nat := 118140960795 + 3752961 * 2 ^ 59
def prefixEnd_3752961 : Nat := 4983230072969 + 3 ^ 40 * 3752961 * 2
def baseEnd_3752961 : Nat := 1284715247052264171018635

theorem tailTrace_3752961 : CollatzResearch.WordTrace tailWord_3752961 prefixEnd_3752961 1284715247052264171018635 := by
  unfold tailWord_3752961
  simp only [CollatzResearch.WordTrace]
  refine ⟨136881732956670726554898737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91254488637780484369932491 136881732956670726554898737)
  ·
    refine ⟨102661299717503044916174053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136881732956670726554898737 102661299717503044916174053)
    ·
      refine ⟨19248993697031820921782635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102661299717503044916174053 19248993697031820921782635)
      ·
        refine ⟨28873490545547731382673953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19248993697031820921782635 28873490545547731382673953)
        ·
          refine ⟨21655117909160798537005465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28873490545547731382673953 21655117909160798537005465)
          ·
            refine ⟨16241338431870598902754099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21655117909160798537005465 16241338431870598902754099)
            ·
              refine ⟨24362007647805898354131149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16241338431870598902754099 24362007647805898354131149)
              ·
                refine ⟨9135752867927211882799181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24362007647805898354131149 9135752867927211882799181)
                ·
                  refine ⟨3425907325472704456049693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9135752867927211882799181 3425907325472704456049693)
                  ·
                    refine ⟨1284715247052264171018635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3425907325472704456049693 1284715247052264171018635)
                    ·
                      rfl

theorem cell22_3752961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 3, 3, 3].length) (baseStart_3752961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3752961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3752961 prefixEnd_3752961 := by exact prefixLift 3752961
  have htrace : WordTrace (prefixWord ++ tailWord_3752961) baseStart_3752961 baseEnd_3752961 := by
    simpa [prefixWord, tailWord_3752961, baseEnd_3752961] using wordTrace_append hprefix tailTrace_3752961
  have hstable : (prefixWord ++ tailWord_3752961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752961).length < 2 ^ (prefixWord ++ tailWord_3752961).sum := by decide
  have hdescent : baseEnd_3752961 < baseStart_3752961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752995 : List Nat := [1, 1, 1, 4, 3, 4, 1, 3, 1, 3]
def baseStart_3752995 : Nat := 118140960795 + 3752995 * 2 ^ 59
def prefixEnd_3752995 : Nat := 4983230072969 + 3 ^ 40 * 3752995 * 2
def baseEnd_3752995 : Nat := 1284726885947099415668531

theorem tailTrace_3752995 : CollatzResearch.WordTrace tailWord_3752995 prefixEnd_3752995 1284726885947099415668531 := by
  unfold tailWord_3752995
  simp only [CollatzResearch.WordTrace]
  refine ⟨136882973038547550361636439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91255315359031700241090959 136882973038547550361636439)
  ·
    refine ⟨205324459557821325542454659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136882973038547550361636439 205324459557821325542454659)
    ·
      refine ⟨307986689336731988313681989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205324459557821325542454659 307986689336731988313681989)
      ·
        refine ⟨57747504250637247808815373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 307986689336731988313681989 57747504250637247808815373)
        ·
          refine ⟨21655314093988967928305765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57747504250637247808815373 21655314093988967928305765)
          ·
            refine ⟨4060371392622931486557331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21655314093988967928305765 4060371392622931486557331)
            ·
              refine ⟨6090557088934397229835997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4060371392622931486557331 6090557088934397229835997)
              ·
                refine ⟨2283958908350398961188499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6090557088934397229835997 2283958908350398961188499)
                ·
                  refine ⟨3425938362525598441782749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2283958908350398961188499 3425938362525598441782749)
                  ·
                    refine ⟨1284726885947099415668531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3425938362525598441782749 1284726885947099415668531)
                    ·
                      rfl

theorem cell22_3752995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 3, 1, 3].length) (baseStart_3752995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3752995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3752995 prefixEnd_3752995 := by exact prefixLift 3752995
  have htrace : WordTrace (prefixWord ++ tailWord_3752995) baseStart_3752995 baseEnd_3752995 := by
    simpa [prefixWord, tailWord_3752995, baseEnd_3752995] using wordTrace_append hprefix tailTrace_3752995
  have hstable : (prefixWord ++ tailWord_3752995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752995).length < 2 ^ (prefixWord ++ tailWord_3752995).sum := by decide
  have hdescent : baseEnd_3752995 < baseStart_3752995 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753025 : List Nat := [1, 2, 5, 1, 3, 2, 2, 1, 5]
def baseStart_3753025 : Nat := 118140960795 + 3753025 * 2 ^ 59
def prefixEnd_3753025 : Nat := 4983230072969 + 3 ^ 40 * 3753025 * 2
def baseEnd_3753025 : Nat := 428245718520063112472813

theorem tailTrace_3753025 : CollatzResearch.WordTrace tailWord_3753025 prefixEnd_3753025 428245718520063112472813 := by
  unfold tailWord_3753025
  simp only [CollatzResearch.WordTrace]
  refine ⟨136884067228438865485228529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91256044818959243656819019 136884067228438865485228529)
  ·
    refine ⟨102663050421329149113921397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136884067228438865485228529 102663050421329149113921397)
    ·
      refine ⟨9624660976999607729430131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102663050421329149113921397 9624660976999607729430131)
      ·
        refine ⟨14436991465499411594145197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9624660976999607729430131 14436991465499411594145197)
        ·
          refine ⟨5413871799562279347804449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14436991465499411594145197 5413871799562279347804449)
          ·
            refine ⟨4060403849671709510853337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5413871799562279347804449 4060403849671709510853337)
            ·
              refine ⟨3045302887253782133140003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4060403849671709510853337 3045302887253782133140003)
              ·
                refine ⟨4567954330880673199710005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3045302887253782133140003 4567954330880673199710005)
                ·
                  refine ⟨428245718520063112472813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4567954330880673199710005 428245718520063112472813)
                  ·
                    rfl

theorem cell22_3753025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 2, 1, 5].length) (baseStart_3753025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3753025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3753025 prefixEnd_3753025 := by exact prefixLift 3753025
  have htrace : WordTrace (prefixWord ++ tailWord_3753025) baseStart_3753025 baseEnd_3753025 := by
    simpa [prefixWord, tailWord_3753025, baseEnd_3753025] using wordTrace_append hprefix tailTrace_3753025
  have hstable : (prefixWord ++ tailWord_3753025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753025).length < 2 ^ (prefixWord ++ tailWord_3753025).sum := by decide
  have hdescent : baseEnd_3753025 < baseStart_3753025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753068 : List Nat := [2, 2, 1, 1, 3, 2, 4, 2, 2, 3]
def baseStart_3753068 : Nat := 118140960795 + 3753068 * 2 ^ 59
def prefixEnd_3753068 : Nat := 4983230072969 + 3 ^ 40 * 3753068 * 2
def baseEnd_3753068 : Nat := 1284751875338951558593307

theorem tailTrace_3753068 : CollatzResearch.WordTrace tailWord_3753068 prefixEnd_3753068 1284751875338951558593307 := by
  unfold tailWord_3753068
  simp only [CollatzResearch.WordTrace]
  refine ⟨68442817783641541914521929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91257090378188722552695905 68442817783641541914521929)
  ·
    refine ⟨51332113337731156435891447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68442817783641541914521929 51332113337731156435891447)
    ·
      refine ⟨76998170006596734653837171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51332113337731156435891447 76998170006596734653837171)
      ·
        refine ⟨115497255009895101980755757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76998170006596734653837171 115497255009895101980755757)
        ·
          refine ⟨43311470628710663242783409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115497255009895101980755757 43311470628710663242783409)
          ·
            refine ⟨32483602971532997432087557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43311470628710663242783409 32483602971532997432087557)
            ·
              refine ⟨6090675557162437018516417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32483602971532997432087557 6090675557162437018516417)
              ·
                refine ⟨4568006667871827763887313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6090675557162437018516417 4568006667871827763887313)
                ·
                  refine ⟨3426005000903870822915485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4568006667871827763887313 3426005000903870822915485)
                  ·
                    refine ⟨1284751875338951558593307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3426005000903870822915485 1284751875338951558593307)
                    ·
                      rfl

theorem cell22_3753068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 3].length) (baseStart_3753068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3753068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3753068 prefixEnd_3753068 := by exact prefixLift 3753068
  have htrace : WordTrace (prefixWord ++ tailWord_3753068) baseStart_3753068 baseEnd_3753068 := by
    simpa [prefixWord, tailWord_3753068, baseEnd_3753068] using wordTrace_append hprefix tailTrace_3753068
  have hstable : (prefixWord ++ tailWord_3753068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753068).length < 2 ^ (prefixWord ++ tailWord_3753068).sum := by decide
  have hdescent : baseEnd_3753068 < baseStart_3753068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753070 : List Nat := [4, 1, 2, 2, 1, 2, 4, 2, 4]
def baseStart_3753070 : Nat := 118140960795 + 3753070 * 2 ^ 59
def prefixEnd_3753070 : Nat := 4983230072969 + 3 ^ 40 * 3753070 * 2
def baseEnd_3753070 : Nat := 428250853326608073347767

theorem tailTrace_3753070 : CollatzResearch.WordTrace tailWord_3753070 prefixEnd_3753070 428250853326608073347767 := by
  unfold tailWord_3753070
  simp only [CollatzResearch.WordTrace]
  refine ⟨17110713564159479771327083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91257139008850558780411109 17110713564159479771327083)
  ·
    refine ⟨25666070346239219656990625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17110713564159479771327083 25666070346239219656990625)
    ·
      refine ⟨19249552759679414742742969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25666070346239219656990625 19249552759679414742742969)
      ·
        refine ⟨14437164569759561057057227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19249552759679414742742969 14437164569759561057057227)
        ·
          refine ⟨21655746854639341585585841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14437164569759561057057227 21655746854639341585585841)
          ·
            refine ⟨16241810140979506189189381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21655746854639341585585841 16241810140979506189189381)
            ·
              refine ⟨3045339401433657410473009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16241810140979506189189381 3045339401433657410473009)
              ·
                refine ⟨2284004551075243057854757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3045339401433657410473009 2284004551075243057854757)
                ·
                  refine ⟨428250853326608073347767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2284004551075243057854757 428250853326608073347767)
                  ·
                    rfl

theorem cell22_3753070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 4, 2, 4].length) (baseStart_3753070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3753070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3753070 prefixEnd_3753070 := by exact prefixLift 3753070
  have htrace : WordTrace (prefixWord ++ tailWord_3753070) baseStart_3753070 baseEnd_3753070 := by
    simpa [prefixWord, tailWord_3753070, baseEnd_3753070] using wordTrace_append hprefix tailTrace_3753070
  have hstable : (prefixWord ++ tailWord_3753070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753070).length < 2 ^ (prefixWord ++ tailWord_3753070).sum := by decide
  have hdescent : baseEnd_3753070 < baseStart_3753070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753130 : List Nat := [3, 1, 5, 1, 1, 1, 1, 3, 3, 3]
def baseStart_3753130 : Nat := 118140960795 + 3753130 * 2 ^ 59
def prefixEnd_3753130 : Nat := 4983230072969 + 3 ^ 40 * 3753130 * 2
def baseEnd_3753130 : Nat := 1284773099206004063543117

theorem tailTrace_3753130 : CollatzResearch.WordTrace tailWord_3753130 prefixEnd_3753130 1284773099206004063543117 := by
  unfold tailWord_3753130
  simp only [CollatzResearch.WordTrace]
  refine ⟨34221974223264617104450211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91258597928705645611867229 34221974223264617104450211)
  ·
    refine ⟨51332961334896925656675317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34221974223264617104450211 51332961334896925656675317)
    ·
      refine ⟨4812465125146586780313311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51332961334896925656675317 4812465125146586780313311)
      ·
        refine ⟨7218697687719880170469967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4812465125146586780313311 7218697687719880170469967)
        ·
          refine ⟨10828046531579820255704951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7218697687719880170469967 10828046531579820255704951)
          ·
            refine ⟨16242069797369730383557427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10828046531579820255704951 16242069797369730383557427)
            ·
              refine ⟨24363104696054595575336141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16242069797369730383557427 24363104696054595575336141)
              ·
                refine ⟨9136164261020473340751053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24363104696054595575336141 9136164261020473340751053)
                ·
                  refine ⟨3426061597882677502781645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9136164261020473340751053 3426061597882677502781645)
                  ·
                    refine ⟨1284773099206004063543117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3426061597882677502781645 1284773099206004063543117)
                    ·
                      rfl

theorem cell22_3753130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_3753130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3753130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3753130 prefixEnd_3753130 := by exact prefixLift 3753130
  have htrace : WordTrace (prefixWord ++ tailWord_3753130) baseStart_3753130 baseEnd_3753130 := by
    simpa [prefixWord, tailWord_3753130, baseEnd_3753130] using wordTrace_append hprefix tailTrace_3753130
  have hstable : (prefixWord ++ tailWord_3753130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753130).length < 2 ^ (prefixWord ++ tailWord_3753130).sum := by decide
  have hdescent : baseEnd_3753130 < baseStart_3753130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
